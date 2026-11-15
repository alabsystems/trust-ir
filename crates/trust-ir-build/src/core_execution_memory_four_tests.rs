// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fetched original Core and independent ByteV1 kernel controls. These tests
//! check closed model terms, including their DAG-v2 round trip; they do not
//! grant native, caller-memory, compiler-transcription or proof authority.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{CastOp, Endianness, Module, StructPassingPolicy, TargetInfo, Ty};

#[path = "core_execution_memory_word_tests.rs"]
mod word_tests;

#[path = "core_execution_memory_word_dispatch_tests.rs"]
mod word_dispatch_tests;

#[derive(Clone, Copy)]
enum TestApi {
    LegacyFour,
    Word,
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

fn replay(scope: &Scope, proof: &PendingEquality, accepted: bool) {
    let term = scope.close(proof.term()).unwrap();
    let claim = scope.close(&proof.proposition()).unwrap();
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let checker = checker();
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();
    if accepted {
        checker.check_type(&term, &claim).unwrap();
        let audit = environment().audit_certification(&claim, &term);
        assert!(audit.is_certified(), "{audit:#?}");
    } else {
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
    }
    assert!(
        !checker.heartbeat_spent(),
        "a resource stop is not a verdict"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
}

fn replay_dag(scope: &Scope, proof: &PendingEquality) {
    replay(scope, proof, true);
    let term = scope.close(proof.term()).unwrap();
    let claim = scope.close(&proof.proposition()).unwrap();
    let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
    assert!(!decoded.has_fvar_quick());
    let checker = checker();
    checker.check_type(&decoded, &claim).unwrap();
    assert!(
        !checker.heartbeat_spent(),
        "a resource stop is not a verdict"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    assert!(
        environment()
            .audit_certification(&claim, &decoded)
            .is_certified()
    );
}

fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}

fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}

fn bounded(word: Expr, literal: u32) -> PendingProof {
    bounded_word(32, word, literal)
}

fn bounded_word(bits: u32, word: Expr, literal: u32) -> PendingProof {
    assert!(matches!(bits, 8 | 16 | 32));
    let max = (1_u64 << bits) - 1;
    assert!(u64::from(literal) <= max);
    PendingProof::candidate(
        app(
            "Nat.lt",
            [word.clone(), app("ir_nat_pow2", [nat(u64::from(bits))])],
        ),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [word]), nat(max - u64::from(literal))],
        ),
    )
}

fn providers() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        constant("Nat"),
        Expr::lam(
            BinderInfo::Default,
            app("IRList", [constant("IRScalar")]),
            Expr::lam(
                BinderInfo::Default,
                constant("IRByteMemoryV1"),
                Expr::lam(
                    BinderInfo::Default,
                    constant("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            constant("Nat"),
                            app("IROutcome.stuck", [constant("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
}

fn memory(kind: usize) -> Expr {
    let allocation = |base, size, owner, live| {
        app(
            "IRByteAllocationV1.mk",
            [
                nat(base),
                nat(size),
                nat(owner),
                constant(if live { "Bool.true" } else { "Bool.false" }),
            ],
        )
    };
    let mut rows = vec![
        allocation(16, 16, 8, true),
        allocation(80, if kind == 2 { 3 } else { 8 }, 0, kind != 1),
        allocation(128, 8, 7, false),
    ];
    if kind == 3 {
        rows.push(allocation(80, 8, 0, true));
    }
    let byte_map = if kind == 4 {
        Expr::lam(
            BinderInfo::Default,
            constant("Nat"),
            choose(
                &option("Nat"),
                app("ir_nat_eqb", [Expr::bvar(0), nat(82)]),
                app("IROption.none", [constant("Nat")]),
                some("Nat", nat(173)),
            ),
        )
    } else {
        Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173)))
    };
    app(
        "IRByteMemoryV1.mk",
        [list("IRByteAllocationV1", &rows), byte_map, nat(1)],
    )
}

fn world(memory: Expr) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            memory,
            nat(37),
            list("Nat", &[nat(8)]),
            nat(9),
        ],
    )
}

fn current_memory(current: &Current) -> Expr {
    app(
        "ir_byte_world_memory_v1",
        [constant("Nat"), current.world.clone()],
    )
}

fn binding(id: ValueId, value: Expr) -> Expr {
    app("IRBinding.mk", [nat(u64::from(id.index())), value])
}

struct Fixture {
    module: Module,
    function: FuncId,
    block: BlockId,
    pointer: ValueId,
    value: ValueId,
    loaded: ValueId,
    extended: ValueId,
    ty: Expr,
    bits: u32,
    bytes: u64,
}

fn fixture(signed: bool, sign_extend: bool) -> Fixture {
    fixture_word(32, signed, sign_extend)
}

fn fixture_word(bits: u32, signed: bool, sign_extend: bool) -> Fixture {
    let mut builder = ModuleBuilder::new_with_target_info(
        "four_byte_fetched_core",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let word = match (bits, signed) {
        (8, true) => Ty::I8,
        (8, false) => Ty::U8,
        (16, true) => Ty::I16,
        (16, false) => Ty::U16,
        (32, true) => Ty::I32,
        (32, false) => Ty::U32,
        _ => panic!("unsupported test word width"),
    };
    let byte_count = u64::from(bits / 8);
    let result_ty = if sign_extend { Ty::I64 } else { Ty::U64 };
    let signature = builder.add_func_type(vec![Ty::Ptr, word.clone()], vec![result_ty.clone()]);
    let function = builder.declare_function("store_load_extend_return", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let pointer = body.add_block_param(block, Ty::Ptr);
    let value = body.add_block_param(block, word.clone());
    body.switch_to_block(block);
    body.store_aligned(word.clone(), pointer, value, byte_count);
    let loaded = body.load_aligned(word.clone(), pointer, byte_count);
    let extended = body.cast(
        if sign_extend {
            CastOp::SExt
        } else {
            CastOp::ZExt
        },
        word,
        result_ty,
        loaded,
    );
    body.ret(vec![extended]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        crate::validate_module(&module).is_empty(),
        "ordinary valid original Core"
    );
    assert_eq!(
        module.functions[function.index() as usize].blocks[block.index() as usize]
            .body
            .len(),
        4
    );
    Fixture {
        module,
        function,
        block,
        pointer,
        value,
        loaded,
        extended,
        ty: app(
            if signed { "IRTy.int_" } else { "IRTy.uint_" },
            [nat(u64::from(bits))],
        ),
        bits,
        bytes: byte_count,
    }
}

impl Fixture {
    fn coordinate(&self, instruction: usize) -> Coordinate {
        Coordinate {
            function: self.function,
            block: self.block,
            instruction,
        }
    }

    fn current(&self, address: u64, word: u32, memory: Expr) -> Current {
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(u64::from(self.function.index())),
                    nat(u64::from(self.block.index())),
                    nat(0),
                    list(
                        "IRBinding",
                        &[
                            binding(self.pointer, app("IRScalar.ptr_", [nat(address)])),
                            binding(self.value, scalar(nat(u64::from(word)))),
                        ],
                    ),
                    list("Nat", &[]),
                ],
            ),
            tail: list("IRFrame", &[]),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            world: world(memory),
        }
    }
}

fn codec(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    ty: Expr,
    word: u32,
) -> ByteFourCodec {
    codec_for(assembler, model, ty, 32, word, TestApi::LegacyFour)
}

fn codec_for(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    ty: Expr,
    bits: u32,
    word: u32,
    api: TestApi,
) -> ByteWordCodec {
    let shape = layout(ty.clone(), u64::from(bits / 8));
    let found = conversion(
        option("IRByteLayoutV1"),
        app("ir_byte_layout_v1", [model.context().clone(), ty.clone()]),
        some("IRByteLayoutV1", shape),
    );
    let bounded = bounded_word(bits, nat(u64::from(word)), word);
    match api {
        TestApi::LegacyFour => assembler.byte_integer32_codec(
            model.context().clone(),
            ty,
            nat(u64::from(word)),
            found,
            bounded,
        ),
        TestApi::Word => assembler.byte_integer_word_codec(
            model.context().clone(),
            ty,
            nat(u64::from(word)),
            found,
            bounded,
        ),
    }
    .unwrap()
}

fn accessible(codec: &ByteFourCodec, input: &ByteLoadFour) -> PendingEquality {
    truth(app(
        "ir_byte_accessible_v1",
        [
            allocs(input.memory.clone()),
            input.address.clone(),
            nat(codec.byte_count().unwrap()),
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
    codec: &ByteFourCodec,
    input: ByteLoadFour,
) -> ByteStoreFourResult {
    store_for(assembler, codec, input, TestApi::LegacyFour)
}

fn store_for(
    assembler: &mut Assembler<'_>,
    codec: &ByteWordCodec,
    input: ByteLoadWord,
    api: TestApi,
) -> ByteStoreWordResult {
    let pointer = conversion(
        option("Nat"),
        pointer_address(input.pointer.clone()),
        some("Nat", input.address.clone()),
    );
    let access = accessible(codec, &input);
    let input = ByteStoreWord {
        pointer: input.pointer,
        address: input.address,
        requested_align: input.requested_align,
        memory: input.memory,
    };
    let premises = ByteStoreWordPremises {
        pointer,
        accessible: access,
    };
    match api {
        TestApi::LegacyFour => assembler.byte_store_four(codec, input, premises),
        TestApi::Word => assembler.byte_store_word(codec, input, premises),
    }
    .unwrap()
}

fn load_input(pointer: Expr, address: u64, memory: Expr) -> ByteLoadFour {
    load_input_word(pointer, address, memory, 4)
}

fn load_input_word(pointer: Expr, address: u64, memory: Expr, byte_count: u64) -> ByteLoadWord {
    ByteLoadFour {
        pointer,
        address: nat(address),
        requested_align: nat(byte_count),
        memory,
    }
}

fn load_for(
    assembler: &mut Assembler<'_>,
    codec: &ByteWordCodec,
    input: ByteLoadWord,
    premises: ByteLoadWordPremises,
    api: TestApi,
) -> Result<PendingEquality> {
    match api {
        TestApi::LegacyFour => assembler.byte_load_four(codec, input, premises),
        TestApi::Word => assembler.byte_load_word(codec, input, premises),
    }
}

fn transfer(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    site: &FetchedSite,
    before: &Current,
    result: MemoryResult,
    evaluated: PendingEquality,
    allocations: PendingEquality,
) -> MemoryTransfer {
    let checks = site.memory_checks(model, before, &result).unwrap();
    let bridge = assembler
        .conversion(
            constant("IRByteMemoryResultV1"),
            checks.evaluation,
            evaluated.left.clone(),
        )
        .unwrap();
    let evaluated = assembler.compose(bridge, evaluated).unwrap();
    site.memory_value(
        assembler,
        model,
        before,
        result,
        MemoryPremises {
            evaluated,
            allocations,
            result: truth(checks.result),
            before: truth(before.valid(model)),
        },
    )
    .unwrap()
}

fn fetched_sequence(signed: bool, sign_extend: bool, word: u32) {
    fetched_sequence_word(32, signed, sign_extend, word, TestApi::LegacyFour);
}

fn fetched_sequence_word(bits: u32, signed: bool, sign_extend: bool, word: u32, api: TestApi) {
    let f = fixture_word(bits, signed, sign_extend);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let sites = (0..4)
        .map(|pc| catalog.fetch(f.coordinate(pc)).unwrap())
        .collect::<Vec<_>>();
    let target = catalog.call_target(f.function).unwrap();
    let before = f.current(80, word, memory(0));
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let codec = codec_for(&mut assembler, &model, f.ty.clone(), bits, word, api);
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
        api,
    );
    let first = transfer(
        &mut assembler,
        &model,
        &sites[0],
        &before,
        stored.result.clone(),
        stored.evaluated.clone(),
        stored.allocations.clone(),
    );
    let input = load_input_word(
        app(
            "ir_getd",
            [first.current().machine(), nat(u64::from(f.pointer.index()))],
        ),
        80,
        current_memory(first.current()),
        f.bytes,
    );
    let pointer = conversion(
        option("Nat"),
        pointer_address(input.pointer.clone()),
        some("Nat", nat(80)),
    );
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
        .compose(initialized_bridge, stored.raw_read.clone())
        .unwrap();
    let loaded = load_for(
        &mut assembler,
        &codec,
        input.clone(),
        ByteLoadWordPremises {
            pointer,
            accessible: accessible(&codec, &input),
            initialized,
        },
        api,
    )
    .unwrap();
    let result = MemoryResult {
        value: codec.value.clone(),
        memory: input.memory,
    };
    let allocations = conversion(
        app("IRList", [constant("IRByteAllocationV1")]),
        allocs(result.memory.clone()),
        allocs(current_memory(first.current())),
    );
    let second = transfer(
        &mut assembler,
        &model,
        &sites[1],
        first.current(),
        result,
        loaded,
        allocations,
    );
    let answer = if sign_extend && u64::from(word) & (1_u64 << (f.bits - 1)) != 0 {
        u64::from(word) | (!0_u64 << f.bits)
    } else {
        u64::from(word)
    };
    let value = scalar(nat(answer));
    let checks = sites[2]
        .scalar_checks(&model, second.current(), value.clone())
        .unwrap();
    let evaluated = conversion(
        constant("IRStepResult"),
        checks.evaluation,
        app("IRStepResult.value", [value.clone()]),
    );
    let third = sites[2]
        .scalar_value(
            &mut assembler,
            &model,
            second.current(),
            value.clone(),
            ScalarPremises {
                evaluated,
                operands: truth(checks.operands),
                result: truth(checks.result),
                before: second.valid().clone(),
            },
        )
        .unwrap();
    // The terminal helper takes the explicit singleton-root shape. Retain the
    // actual preceding state and kernel-check its conversion to that shape.
    let root = RootReturnFrame {
        returning: third.current().frame.clone(),
        legacy_memory: third.current().legacy_memory.clone(),
        legacy_cursor: third.current().legacy_cursor.clone(),
        memory: current_memory(third.current()),
        host: nat(37),
        owner: nat(8),
        next: nat(9),
    };
    let root_current = root.current(&model);
    let values = list("IRScalar", std::slice::from_ref(&value));
    let resolved = conversion(
        app("IRList", [constant("IRScalar")]),
        app(
            "ir_resolve",
            [
                root_current.machine(),
                list("Nat", &[nat(u64::from(f.extended.index()))]),
            ],
        ),
        values.clone(),
    );
    let admitted = truth(
        sites[3]
            .root_return_admission(&model, &target, &root, values.clone())
            .unwrap(),
    );
    let returned = sites[3]
        .return_from_root(
            &mut assembler,
            &model,
            &target,
            &root,
            resolved,
            admitted,
            truth(root_current.valid(&model)),
        )
        .unwrap();
    let prefix = assembler
        .concatenate(first.run().clone(), second.run().clone())
        .unwrap();
    let prefix = assembler.concatenate(prefix, third.run().clone()).unwrap();
    let boundary = assembler
        .conversion(
            model.config_type(),
            prefix.reached().clone(),
            root_current.running(&model),
        )
        .unwrap();
    let equality = assembler
        .compose(prefix.equality().clone(), boundary)
        .unwrap();
    let prefix = ExactRun::candidate(
        model.clone(),
        before.running(&model),
        root_current.running(&model),
        prefix.fuel().clone(),
        equality,
    )
    .unwrap();
    let whole = assembler
        .concatenate(prefix, returned.run().clone())
        .unwrap();
    let expected_memory = app(
        "ir_byte_retire_v1",
        [
            nat(8),
            written_word(memory(0), nat(80), f.bytes, nat(u64::from(word))),
        ],
    );
    let expected = app(
        "IRByteConfigV1.halted",
        [
            constant("Nat"),
            app("IROutcome.ret", [values]),
            app(
                "IRByteWorldV1.mk",
                [
                    constant("Nat"),
                    expected_memory,
                    nat(37),
                    list("Nat", &[]),
                    nat(9),
                ],
            ),
        ],
    );
    let expected_run = PendingEquality::candidate(
        model.config_type(),
        model.run(&NatTerm::literal(4), before.running(&model)),
        expected,
        whole.equality().term().clone(),
    );
    // Independent lookup assertions name both real definitions, not only the
    // final summary. These conversion candidates are also kernel checked.
    let loaded_binding = conversion(
        constant("IRScalar"),
        app(
            "ir_getd",
            [second.current().machine(), nat(u64::from(f.loaded.index()))],
        ),
        scalar(nat(u64::from(word))),
    );
    let extended_binding = conversion(
        constant("IRScalar"),
        app(
            "ir_getd",
            [
                third.current().machine(),
                nat(u64::from(f.extended.index())),
            ],
        ),
        value,
    );
    drop(assembler);
    replay(&scope, first.step(), true);
    replay(&scope, second.step(), true);
    replay(&scope, third.step(), true);
    replay(&scope, &loaded_binding, true);
    replay(&scope, &extended_binding, true);
    replay_dag(&scope, &expected_run);
}

#[test]
fn four_byte_fetched_u32_store_load_zero_extend_and_root_return_replay_dag_v2() {
    for word in [0, 0x0102_0304, 0x8000_0000, u32::MAX] {
        fetched_sequence(false, false, word);
    }
}

#[test]
fn four_byte_fetched_i32_high_bits_distinguish_sign_and_zero_extension() {
    for word in [0x8000_0000, u32::MAX] {
        fetched_sequence(true, true, word);
        fetched_sequence(true, false, word);
    }
}

#[test]
fn four_byte_store_has_little_endian_digits_and_preserves_both_neighbors() {
    let f = fixture(false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let codec = codec(&mut assembler, &model, f.ty, 0x0102_0304);
    let stored = store(
        &mut assembler,
        &codec,
        load_input(app("IRScalar.ptr_", [nat(80)]), 80, memory(0)),
    );
    let digits = [(79, 173), (80, 4), (81, 3), (82, 2), (83, 1), (84, 173)].map(|(at, byte)| {
        conversion(
            option("Nat"),
            Expr::app(bytes(stored.result.memory.clone()), nat(at)),
            some("Nat", nat(byte)),
        )
    });
    let wrong_order = conversion(
        option("Nat"),
        Expr::app(bytes(stored.result.memory.clone()), nat(80)),
        some("Nat", nat(1)),
    );
    drop(assembler);
    replay_dag(&scope, &stored.evaluated);
    replay_dag(&scope, &stored.raw_read);
    replay_dag(&scope, &stored.typed_readback);
    replay(&scope, &stored.allocations, true);
    replay(&scope, &stored.cursor, true);
    for digit in digits {
        replay(&scope, &digit, true);
    }
    replay(&scope, &wrong_order, false);
}

#[test]
fn four_byte_store_replays_universal_word_and_arbitrary_prior_bytes() {
    universal_prior_bytes(32, false, TestApi::LegacyFour);
}

fn universal_prior_bytes(bits: u32, signed: bool, api: TestApi) {
    let f = fixture_word(bits, signed, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let old_bytes = assembler
        .local(Expr::pi(
            BinderInfo::Default,
            constant("Nat"),
            option("Nat"),
        ))
        .unwrap();
    let word = assembler.local(constant("Nat")).unwrap();
    let bound = assembler
        .local(app(
            "Nat.lt",
            [word.term().clone(), integer_word_limit(f.bytes)],
        ))
        .unwrap();
    let found = conversion(
        option("IRByteLayoutV1"),
        app("ir_byte_layout_v1", [model.context().clone(), f.ty.clone()]),
        some("IRByteLayoutV1", layout(f.ty.clone(), f.bytes)),
    );
    let bounded = PendingProof::candidate(
        app("Nat.lt", [word.term().clone(), integer_word_limit(f.bytes)]),
        bound.term().clone(),
    );
    let codec = match api {
        TestApi::LegacyFour => assembler.byte_integer32_codec(
            model.context().clone(),
            f.ty,
            word.term().clone(),
            found,
            bounded,
        ),
        TestApi::Word => assembler.byte_integer_word_codec(
            model.context().clone(),
            f.ty,
            word.term().clone(),
            found,
            bounded,
        ),
    }
    .unwrap();
    let input_memory = app(
        "IRByteMemoryV1.mk",
        [allocs(memory(0)), old_bytes.term().clone(), nat(1)],
    );
    let stored = store_for(
        &mut assembler,
        &codec,
        load_input_word(app("IRScalar.ptr_", [nat(80)]), 80, input_memory, f.bytes),
        api,
    );
    let outside = [79, 80 + f.bytes].map(|at| {
        PendingEquality::candidate(
            option("Nat"),
            Expr::app(bytes(stored.result.memory.clone()), nat(at)),
            Expr::app(old_bytes.term().clone(), nat(at)),
            app(
                "ir_byte_write_outside_v1",
                [
                    old_bytes.term().clone(),
                    nat(80),
                    nat(f.bytes),
                    word.term().clone(),
                    nat(at),
                    refl(&constant("Bool"), constant("Bool.false")),
                ],
            ),
        )
    });
    drop(assembler);
    for proof in [
        &stored.evaluated,
        &stored.raw_read,
        &stored.typed_readback,
        &outside[0],
        &outside[1],
    ] {
        // Abstract the bound rather than installing it as a global axiom. Both
        // arbitrary byte maps and every canonical word remain in the claim.
        let term = scope
            .close(&old_bytes.lam(word.lam(bound.lam(proof.term().clone()))))
            .unwrap();
        let claim = scope
            .close(&old_bytes.pi(word.pi(bound.pi(proof.proposition()))))
            .unwrap();
        assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
        let checker = checker();
        checker
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        checker.check_type(&term, &claim).unwrap();
        assert!(
            !checker.heartbeat_spent(),
            "a resource stop is not a verdict"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        assert!(
            environment()
                .audit_certification(&claim, &term)
                .is_certified()
        );
        let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
        checker.check_type(&decoded, &claim).unwrap();
        assert!(
            !checker.heartbeat_spent(),
            "a resource stop is not a verdict"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        assert!(
            environment()
                .audit_certification(&claim, &decoded)
                .is_certified()
        );
    }
}

#[test]
fn four_byte_alias_readback_uses_last_store_not_entry_or_previous_memory() {
    let f = fixture(false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let first_codec = codec(&mut assembler, &model, f.ty.clone(), 0x0102_0304);
    let first = store(
        &mut assembler,
        &first_codec,
        load_input(app("IRScalar.ptr_", [nat(80)]), 80, memory(0)),
    );
    let second_codec = codec(&mut assembler, &model, f.ty, 0x8000_0000);
    let second = store(
        &mut assembler,
        &second_codec,
        load_input(
            app("IRScalar.ptr_", [nat(80)]),
            80,
            first.result.memory.clone(),
        ),
    );
    let input = load_input(
        app("IRScalar.ptr_", [nat(80)]),
        80,
        second.result.memory.clone(),
    );
    let pointer = conversion(
        option("Nat"),
        pointer_address(input.pointer.clone()),
        some("Nat", nat(80)),
    );
    let access = accessible(&second_codec, &input);
    assert!(
        assembler
            .byte_load_four(
                &second_codec,
                input.clone(),
                ByteLoadFourPremises {
                    pointer: pointer.clone(),
                    accessible: access.clone(),
                    initialized: first.raw_read.clone()
                }
            )
            .is_err(),
        "stale memory endpoint is a structural refusal, not a replay"
    );
    let initialized_bridge = assembler
        .conversion(
            option("Nat"),
            app(
                "ir_byte_read_word_v1",
                [bytes(input.memory.clone()), nat(4), nat(80)],
            ),
            second.raw_read.left().clone(),
        )
        .unwrap();
    let initialized = assembler
        .compose(initialized_bridge, second.raw_read.clone())
        .unwrap();
    let loaded = assembler
        .byte_load_four(
            &second_codec,
            input.clone(),
            ByteLoadFourPremises {
                pointer: pointer.clone(),
                accessible: access.clone(),
                initialized: initialized.clone(),
            },
        )
        .unwrap();
    let forged_same_endpoint = PendingEquality::candidate(
        option("Nat"),
        initialized.left().clone(),
        initialized.right().clone(),
        first.raw_read.term().clone(),
    );
    let forged = assembler
        .byte_load_four(
            &second_codec,
            input.clone(),
            ByteLoadFourPremises {
                pointer,
                accessible: access,
                initialized: forged_same_endpoint,
            },
        )
        .unwrap();
    let stale = conversion(
        option("Nat"),
        app(
            "ir_byte_read_word_v1",
            [bytes(input.memory), nat(4), nat(80)],
        ),
        some("Nat", nat(0x0102_0304)),
    );
    drop(assembler);
    replay(&scope, &first.evaluated, true);
    replay(&scope, &second.evaluated, true);
    replay_dag(&scope, &loaded);
    replay(&scope, &forged, false);
    replay(&scope, &stale, false);
}

#[test]
fn four_byte_fetched_store_requires_complete_live_unique_aligned_extent() {
    let f = fixture(false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(0))
        .unwrap();
    for (kind, address) in [(1, 80), (2, 80), (3, 80), (0, 81)] {
        let before = f.current(address, 7, memory(kind));
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let codec = codec(&mut assembler, &model, f.ty.clone(), 7);
        let candidate = store(
            &mut assembler,
            &codec,
            load_input(
                app(
                    "ir_getd",
                    [before.machine(), nat(u64::from(f.pointer.index()))],
                ),
                address,
                current_memory(&before),
            ),
        );
        let step = transfer(
            &mut assembler,
            &model,
            &site,
            &before,
            candidate.result,
            candidate.evaluated,
            candidate.allocations,
        );
        drop(assembler);
        replay(&scope, step.step(), false);
    }
}

#[test]
fn four_byte_load_requires_every_initialized_byte_and_exact_claimed_word() {
    let f = fixture(false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    // All-AD memory reads ADADADAD, not 7; kind4 additionally omits one byte.
    for (kind, claimed) in [(0, 7), (4, 0xadad_adad)] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let codec = codec(&mut assembler, &model, f.ty.clone(), claimed);
        let input = load_input(app("IRScalar.ptr_", [nat(80)]), 80, memory(kind));
        let initialized = conversion(
            option("Nat"),
            app(
                "ir_byte_read_word_v1",
                [bytes(input.memory.clone()), nat(4), nat(80)],
            ),
            some("Nat", nat(u64::from(claimed))),
        );
        let loaded = assembler
            .byte_load_four(
                &codec,
                input.clone(),
                ByteLoadFourPremises {
                    pointer: conversion(
                        option("Nat"),
                        pointer_address(input.pointer.clone()),
                        some("Nat", nat(80)),
                    ),
                    accessible: accessible(&codec, &input),
                    initialized,
                },
            )
            .unwrap();
        drop(assembler);
        replay(&scope, &loaded, false);
    }
}

#[test]
fn four_byte_codec_type_bound_layout_and_same_endpoint_proofs_are_not_authority() {
    let f = fixture(false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for ty in [
        app("IRTy.int_", [nat(64)]),
        app("IRTy.uint_", [nat(8)]),
        constant("IRTy.ptr_"),
    ] {
        let found = conversion(
            option("IRByteLayoutV1"),
            app("ir_byte_layout_v1", [model.context().clone(), ty.clone()]),
            some("IRByteLayoutV1", layout(ty.clone(), 4)),
        );
        assert!(
            assembler
                .byte_integer32_codec(
                    model.context().clone(),
                    ty,
                    nat(7),
                    found,
                    bounded(nat(7), 7)
                )
                .is_err()
        );
    }
    let found = conversion(
        option("IRByteLayoutV1"),
        app("ir_byte_layout_v1", [model.context().clone(), f.ty.clone()]),
        some("IRByteLayoutV1", layout(f.ty.clone(), 4)),
    );
    let wrong_bound =
        PendingProof::candidate(app("Nat.lt", [nat(7), limit()]), constant("True.intro"));
    assert!(
        assembler
            .byte_integer32_codec(
                model.context().clone(),
                f.ty.clone(),
                nat(7),
                found.clone(),
                wrong_bound
            )
            .is_err()
    );
    let out_of_range = 1_u64 << 32;
    let forged_bound = PendingProof::candidate(
        app("Nat.lt", [nat(out_of_range), word_limit()]),
        app("Nat.zero_le", [nat(0)]),
    );
    let bad = assembler
        .byte_integer32_codec(
            model.context().clone(),
            f.ty.clone(),
            nat(out_of_range),
            found,
            forged_bound,
        )
        .unwrap();
    let noncanonical = store(
        &mut assembler,
        &bad,
        load_input(app("IRScalar.ptr_", [nat(80)]), 80, memory(0)),
    );
    let mut valid = codec(&mut assembler, &model, f.ty, 7);
    valid.layout_found.term = constant("True.intro");
    let forged_layout = store(
        &mut assembler,
        &valid,
        load_input(app("IRScalar.ptr_", [nat(80)]), 80, memory(0)),
    );
    drop(assembler);
    replay(&scope, &noncanonical.evaluated, false);
    replay(&scope, &forged_layout.evaluated, false);
}

#[test]
fn four_byte_reflection_and_construction_stay_fail_closed() {
    let mut f = fixture(false, false);
    f.module.target_info.as_mut().unwrap().endianness = Endianness::Big;
    let error = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap_err();
    assert_eq!(
        error.to_string(),
        "unsupported byte-profile target layout or aggregate passing policy"
    );
    f.module.target_info.as_mut().unwrap().endianness = Endianness::Little;
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let codec = codec(&mut assembler, &model, f.ty, 7);
    drop(assembler);
    let input = load_input(app("IRScalar.ptr_", [nat(80)]), 80, memory(0));
    let pointer = conversion(
        option("Nat"),
        pointer_address(input.pointer.clone()),
        some("Nat", nat(80)),
    );
    let premises = ByteStoreFourPremises {
        pointer,
        accessible: accessible(&codec, &input),
    };
    let mut bounded_limits = limits();
    bounded_limits.max_operations = 1;
    let mut assembler = Assembler::new(&mut scope, bounded_limits).unwrap();
    let error = assembler
        .byte_store_four(
            &codec,
            ByteStoreFour {
                pointer: input.pointer,
                address: input.address,
                requested_align: input.requested_align,
                memory: input.memory,
            },
            premises,
        )
        .err()
        .expect("one operation cannot construct the dispatch");
    assert!(error.contains("operation"), "{error}");
}
