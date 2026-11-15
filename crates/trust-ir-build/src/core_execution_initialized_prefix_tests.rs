// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual fetched Store sequences and final-byte observations. These are
//! closed Core-model candidates, not native scratch-provider or performance
//! evidence. The allocation is an explicit input, not an executed acquisition.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo, Ty};

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

fn replay_claim(scope: &Scope, claim: Expr, term: Expr, accepted: bool) {
    let claim = scope.close(&claim).unwrap();
    let term = scope.close(&term).unwrap();
    assert!(!claim.has_fvar_quick() && !term.has_fvar_quick());
    let checker = checker();
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .expect("the independent claim must itself be a proposition");
    if accepted {
        checker.check_type(&term, &claim).unwrap();
        let audit = environment().audit_certification(&claim, &term);
        assert!(audit.is_certified(), "{audit:#?}");
    } else {
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "expected a proof mismatch, not a resource refusal: {error:?}"
        );
    }
}

fn replay(scope: &Scope, equality: &PendingEquality, accepted: bool) {
    replay_claim(
        scope,
        equality.proposition(),
        equality.term().clone(),
        accepted,
    );
}

fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}

fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}

fn byte_limit() -> Expr {
    constant("ir_byte_limit_v1")
}

fn bounded_word(word: Expr, literal: u64) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [word.clone(), byte_limit()]),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [word]), nat(u64::MAX - literal)],
        ),
    )
}

fn extent(base: u64, count: usize) -> PendingProof {
    let count = u64::try_from(count).unwrap();
    let end = base.checked_add(count.checked_mul(8).unwrap()).unwrap();
    let endpoint = app("Nat.add", [nat(base), app("Nat.mul", [nat(8), nat(count)])]);
    PendingProof::candidate(
        app("Nat.le", [endpoint, byte_limit()]),
        app(
            "Nat.le_add_right",
            [nat(end), app("Nat.succ", [nat(u64::MAX - end)])],
        ),
    )
}

fn allocations(memory: Expr) -> Expr {
    app("ir_byte_mem_allocs_v1", [memory])
}

fn bytes(memory: Expr) -> Expr {
    app("ir_byte_mem_bytes_v1", [memory])
}

fn write(memory: Expr, address: Expr, word: Expr) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            allocations(memory.clone()),
            app(
                "ir_byte_write_word_v1",
                [bytes(memory.clone()), address, nat(8), word],
            ),
            app("ir_byte_mem_next_v1", [memory]),
        ],
    )
}

fn input_memory() -> Expr {
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
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[
                    allocation(16, 16, 0, true),
                    allocation(80, 24, 8, true),
                    allocation(128, 8, 7, false),
                ],
            ),
            Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173))),
            // No high-water premise: this is accessible existing memory.
            nat(1),
        ],
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

fn providers() -> Expr {
    // Total and unused. No scratch-acquire/consume provider theorem is assumed.
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

struct Fixture {
    module: Module,
    function: FuncId,
    block: BlockId,
    pointers: [ValueId; 3],
    words: [ValueId; 3],
}

fn fixture() -> Fixture {
    let mut builder = ModuleBuilder::new_with_target_info(
        "initialized_eight_prefix",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(
        vec![Ty::Ptr, Ty::I64, Ty::Ptr, Ty::I64, Ty::Ptr, Ty::I64],
        vec![],
    );
    let function = builder.declare_function("three_actual_stores", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let pairs: [(ValueId, ValueId); 3] = std::array::from_fn(|_| {
        (
            body.add_block_param(block, Ty::Ptr),
            body.add_block_param(block, Ty::I64),
        )
    });
    body.switch_to_block(block);
    for (pointer, word) in pairs {
        body.store_aligned(Ty::I64, pointer, word, 8);
    }
    body.ret(vec![]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    Fixture {
        module,
        function,
        block,
        pointers: pairs.map(|pair| pair.0),
        words: pairs.map(|pair| pair.1),
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

    fn current(&self, words: [u64; 3], memory: Expr, pc: usize) -> Current {
        let mut bindings = Vec::new();
        for (index, word) in words.into_iter().enumerate() {
            bindings.push(app(
                "IRBinding.mk",
                [
                    nat(u64::from(self.pointers[index].index())),
                    app("IRScalar.ptr_", [nat(80 + 8 * index as u64)]),
                ],
            ));
            bindings.push(app(
                "IRBinding.mk",
                [
                    nat(u64::from(self.words[index].index())),
                    app("IRScalar.int_", [nat(word)]),
                ],
            ));
        }
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(u64::from(self.function.index())),
                    nat(u64::from(self.block.index())),
                    nat(pc as u64),
                    list("IRBinding", &bindings),
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

fn actual_store(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    fixture: &Fixture,
    current: &Current,
    index: usize,
    word: u64,
) -> ByteStoreEightResult {
    let ty = app("IRTy.int_", [nat(64)]);
    let layout = app(
        "IRByteLayoutV1.mk",
        [
            ty.clone(),
            nat(8),
            nat(8),
            list("IRTy", &[]),
            list("Nat", &[]),
        ],
    );
    let codec = assembler
        .byte_i64_codec(
            model.context().clone(),
            nat(word),
            conversion(
                app("IROption", [constant("IRByteLayoutV1")]),
                app("ir_byte_layout_v1", [model.context().clone(), ty]),
                some("IRByteLayoutV1", layout),
            ),
            bounded_word(nat(word), word),
        )
        .unwrap();
    let pointer = app(
        "ir_getd",
        [
            current.machine(),
            nat(u64::from(fixture.pointers[index].index())),
        ],
    );
    let address = nat(80 + 8 * index as u64);
    let memory = current_memory(current);
    let alignment = app(
        "ir_byte_effective_align_v1",
        [
            nat(8),
            app("ir_byte_layout_align_v1", [codec.layout.clone()]),
        ],
    );
    assembler
        .byte_store_eight(
            &codec,
            ByteStoreEight {
                pointer: pointer.clone(),
                address: address.clone(),
                requested_align: nat(8),
                memory: memory.clone(),
            },
            ByteStoreEightPremises {
                pointer: conversion(
                    app("IROption", [constant("Nat")]),
                    app("ir_byte_pointer_address_v1", [pointer]),
                    some("Nat", address.clone()),
                ),
                accessible: truth(app(
                    "ir_byte_accessible_v1",
                    [allocations(memory), address, nat(8), alignment],
                )),
            },
        )
        .unwrap()
}

fn fetched_store(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    site: &FetchedSite,
    before: &Current,
    stored: &ByteStoreEightResult,
) -> MemoryTransfer {
    let checks = site.memory_checks(model, before, &stored.result).unwrap();
    let bridge = assembler
        .conversion(
            constant("IRByteMemoryResultV1"),
            checks.evaluation,
            stored.evaluated.left().clone(),
        )
        .unwrap();
    let evaluated = assembler.compose(bridge, stored.evaluated.clone()).unwrap();
    site.memory_value(
        assembler,
        model,
        before,
        stored.result.clone(),
        MemoryPremises {
            evaluated,
            allocations: stored.allocations.clone(),
            result: truth(checks.result),
            before: truth(before.valid(model)),
        },
    )
    .unwrap()
}

fn append(
    assembler: &mut Assembler<'_>,
    prefix: InitializedEightPrefix,
    word: u64,
    after: Expr,
) -> InitializedEightPrefix {
    let index = prefix.count();
    let address = nat(80 + 8 * index as u64);
    let written = write(prefix.memory().clone(), address.clone(), nat(word));
    let adjacent = app(
        "Nat.add",
        [
            prefix.base().clone(),
            app("Nat.mul", [nat(8), nat(index as u64)]),
        ],
    );
    assembler
        .byte_initialized_eight_append(
            prefix,
            address.clone(),
            nat(word),
            after.clone(),
            InitializedEightAppendPremises {
                adjacent: conversion(constant("Nat"), address, adjacent),
                written: conversion(constant("IRByteMemoryV1"), after, written),
                bounded_word: bounded_word(nat(word), word),
                extent: extent(80, index + 1),
            },
        )
        .unwrap()
}

fn literal_words(words: &[u64]) -> Expr {
    list("Nat", &words.iter().copied().map(nat).collect::<Vec<_>>())
}

fn expected_memory(words: &[u64]) -> Expr {
    words
        .iter()
        .copied()
        .enumerate()
        .fold(input_memory(), |memory, (index, word)| {
            write(memory, nat(80 + 8 * index as u64), nat(word))
        })
}

fn option_words() -> Expr {
    app("IROption", [app("IRList", [constant("Nat")])])
}

fn some_words(words: Expr) -> Expr {
    app("IROption.some", [app("IRList", [constant("Nat")]), words])
}

fn raw_prefix(assembler: &mut Assembler<'_>, words: &[u64]) -> InitializedEightPrefix {
    let mut prefix = assembler
        .byte_initialized_eight_empty(input_memory(), nat(80))
        .unwrap();
    for &word in words {
        let after = write(
            prefix.memory().clone(),
            nat(80 + 8 * prefix.count() as u64),
            nat(word),
        );
        prefix = append(assembler, prefix, word, after);
    }
    prefix
}

fn independent_readback(
    assembler: &mut Assembler<'_>,
    read: &InitializedEightRead,
    memory: Expr,
    words: &[u64],
) -> PendingEquality {
    let observed = assembler
        .byte_initialized_eight_read(memory, nat(80), &NatTerm::literal(words.len() as u64))
        .unwrap();
    PendingEquality::candidate(
        option_words(),
        observed,
        some_words(literal_words(words)),
        read.readback().term().clone(),
    )
}

#[test]
fn initialized_prefix_three_fetched_stores_share_final_memory_and_ordered_words() {
    let fixture = fixture();
    let reflected = reflect_core_module_v1(&fixture.module, &[(fixture.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    for words in [[0, 1_u64 << 63, u64::MAX], [u64::MAX, 0, u64::MAX]] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let initial = fixture.current(words, input_memory(), 0);
        let mut current = initial.clone();
        let mut prefix = assembler
            .byte_initialized_eight_empty(current_memory(&initial), nat(80))
            .unwrap();
        let mut run = assembler.zero(&model, initial.running(&model)).unwrap();
        let mut steps = Vec::new();
        for (index, word) in words.into_iter().enumerate() {
            let site = catalog.fetch(fixture.coordinate(index)).unwrap();
            let stored = actual_store(&mut assembler, &model, &fixture, &current, index, word);
            let transfer = fetched_store(&mut assembler, &model, &site, &current, &stored);
            // Append consumes the actual store's returned memory. No old
            // per-slot readback is framed or supplied to the accumulator.
            prefix = append(&mut assembler, prefix, word, transfer.memory().clone());
            run = assembler.concatenate(run, transfer.run().clone()).unwrap();
            current = transfer.current().clone();
            steps.push(transfer.step().clone());
        }
        let read = assembler.byte_initialized_eight_finish(prefix).unwrap();
        assert_eq!(read.count(), 3);
        assert_eq!(read.base(), &nat(80));
        assert!(read.extent().is_some());
        let final_memory = expected_memory(&words);
        let independent = independent_readback(&mut assembler, &read, final_memory.clone(), &words);
        let final_current = fixture.current(words, final_memory.clone(), 3);
        let exact_run = PendingEquality::candidate(
            model.config_type(),
            model.run(&NatTerm::literal(3), initial.running(&model)),
            final_current.running(&model),
            run.equality().term().clone(),
        );
        let retained_extent = read.bounded_readback().unwrap();
        let unchanged_rows = conversion(
            app("IRList", [constant("IRByteAllocationV1")]),
            allocations(read.memory().clone()),
            allocations(input_memory()),
        );
        assert_eq!(assembler.initialized_eight_helper_builds, 1);
        assert_eq!(assembler.initialized_eight_appends, 3);
        drop(assembler);
        for step in steps {
            replay(&scope, &step, true);
        }
        replay(&scope, &exact_run, true);
        replay(&scope, &independent, true);
        replay(&scope, &unchanged_rows, true);
        replay_claim(
            &scope,
            retained_extent.proposition().clone(),
            retained_extent.term().clone(),
            true,
        );
    }
}

#[test]
fn initialized_prefix_rejects_stale_final_memory_order_and_changed_earlier_word() {
    let words = [0, 1_u64 << 63, u64::MAX];
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let prefix = raw_prefix(&mut assembler, &words);
    let read = assembler.byte_initialized_eight_finish(prefix).unwrap();
    let positive = independent_readback(&mut assembler, &read, expected_memory(&words), &words);
    let stale = independent_readback(&mut assembler, &read, expected_memory(&words[..2]), &words);
    let order = independent_readback(
        &mut assembler,
        &read,
        expected_memory(&words),
        &[u64::MAX, 1_u64 << 63, 0],
    );
    let changed = independent_readback(
        &mut assembler,
        &read,
        write(expected_memory(&words), nat(80), nat(7)),
        &words,
    );
    let final_memory = expected_memory(&words);
    let missing = app(
        "IRByteMemoryV1.mk",
        [
            allocations(final_memory.clone()),
            Expr::lam(
                BinderInfo::Default,
                constant("Nat"),
                choose(
                    &app("IROption", [constant("Nat")]),
                    app("ir_nat_eqb", [Expr::bvar(0), nat(89)]),
                    app("IROption.none", [constant("Nat")]),
                    Expr::app(bytes(final_memory.clone()), Expr::bvar(0)),
                ),
            ),
            app("ir_byte_mem_next_v1", [final_memory]),
        ],
    );
    let missing = independent_readback(&mut assembler, &read, missing, &words);
    drop(assembler);
    replay(&scope, &positive, true);
    for refusal in [stale, order, changed, missing] {
        replay(&scope, &refusal, false);
    }
}

#[test]
fn initialized_prefix_append_refuses_forged_adjacency_word_write_and_extent_proofs() {
    for mutation in ["adjacency", "skipped", "word", "write", "extent"] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let prefix = raw_prefix(&mut assembler, &[7]);
        let address = match mutation {
            "adjacency" => nat(80), // overlaps the first initialized slot
            "skipped" => nat(96),   // leaves the required second slot untouched
            _ => nat(88),
        };
        let word = if mutation == "word" {
            byte_limit()
        } else {
            nat(11)
        };
        let actual_write = write(prefix.memory().clone(), address.clone(), word.clone());
        let after = if mutation == "write" {
            // The second word remains the old 173-byte image, so this is not
            // accidentally a no-op write with a harmless alternative proof.
            prefix.memory().clone()
        } else {
            actual_write.clone()
        };
        let adjacent = app("Nat.add", [nat(80), app("Nat.mul", [nat(8), nat(1)])]);
        let mut word_bound = bounded_word(word.clone(), 11);
        if mutation == "word" {
            word_bound = PendingProof::candidate(
                app("Nat.lt", [byte_limit(), byte_limit()]),
                app("Nat.le_refl", [byte_limit()]),
            );
        }
        let mut extent_proof = extent(80, 2);
        if mutation == "extent" {
            extent_proof = PendingProof::candidate(
                extent_proof.proposition().clone(),
                refl(&constant("Bool"), constant("Bool.true")),
            );
        }
        let prefix = assembler
            .byte_initialized_eight_append(
                prefix,
                address.clone(),
                word,
                after.clone(),
                InitializedEightAppendPremises {
                    adjacent: conversion(constant("Nat"), address, adjacent),
                    written: conversion(constant("IRByteMemoryV1"), after, actual_write),
                    bounded_word: word_bound,
                    extent: extent_proof,
                },
            )
            .unwrap();
        let read = assembler.byte_initialized_eight_finish(prefix).unwrap();
        let bounded = read.bounded_readback().unwrap();
        drop(assembler);
        if mutation == "extent" {
            // Extent is separate evidence: a bad bound must not contaminate
            // the true raw-byte observation, nor disappear from bounded_readback.
            replay(&scope, read.readback(), true);
        }
        replay_claim(
            &scope,
            bounded.proposition().clone(),
            bounded.term().clone(),
            false,
        );
    }

    // Distinct SOURCE admission controls: these are genuine reflexive proofs
    // about other endpoints, not kernel refusals of forged proof terms.
    for wrong_endpoint in ["adjacent", "written"] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let prefix = raw_prefix(&mut assembler, &[7]);
        let before = prefix.memory().clone();
        let after = write(before.clone(), nat(88), nat(11));
        let adjacent = if wrong_endpoint == "adjacent" {
            PendingEquality::reflexive(constant("Nat"), nat(96))
        } else {
            conversion(
                constant("Nat"),
                nat(88),
                app("Nat.add", [nat(80), app("Nat.mul", [nat(8), nat(1)])]),
            )
        };
        let written = if wrong_endpoint == "written" {
            PendingEquality::reflexive(constant("IRByteMemoryV1"), before)
        } else {
            PendingEquality::reflexive(constant("IRByteMemoryV1"), after.clone())
        };
        let refused = assembler.byte_initialized_eight_append(
            prefix,
            nat(88),
            nat(11),
            after,
            InitializedEightAppendPremises {
                adjacent,
                written,
                bounded_word: bounded_word(nat(11), 11),
                extent: extent(80, 2),
            },
        );
        let error = refused
            .err()
            .expect("foreign premise endpoints must be refused");
        assert!(error.contains("equality left endpoint"), "{error}");
    }
}

#[test]
fn initialized_prefix_transport_requires_bytes_not_only_valid_owners() {
    for changed_bytes in [false, true] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let prefix = raw_prefix(&mut assembler, &[11, 12]);
        let before = prefix.memory().clone();
        let after = if changed_bytes {
            write(before.clone(), nat(80), nat(13))
        } else {
            // Raw observations may survive a changed allocation cursor when
            // there is explicit byte equality; no allocation theorem is claimed.
            app(
                "IRByteMemoryV1.mk",
                [allocations(before.clone()), bytes(before.clone()), nat(2)],
            )
        };
        let owners = truth(app(
            "ir_byte_memory_owners_v1",
            [after.clone(), list("Nat", &[nat(8)]), nat(9)],
        ));
        let byte_function = Expr::pi(
            BinderInfo::Default,
            constant("Nat"),
            app("IROption", [constant("Nat")]),
        );
        let equality = conversion(byte_function, bytes(after.clone()), bytes(before));
        let prefix = assembler
            .byte_initialized_eight_transport(prefix, after.clone(), equality)
            .unwrap();
        let read = assembler.byte_initialized_eight_finish(prefix).unwrap();
        let observed = independent_readback(&mut assembler, &read, after, &[11, 12]);
        let bounded = read.bounded_readback().unwrap();
        drop(assembler);
        replay(&scope, &owners, true);
        replay(&scope, &observed, !changed_bytes);
        replay_claim(
            &scope,
            bounded.proposition().clone(),
            bounded.term().clone(),
            !changed_bytes,
        );
    }
}

#[test]
fn initialized_prefix_empty_and_cached_helpers_preserve_explicit_limits() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let empty = assembler
        .byte_initialized_eight_empty(input_memory(), nat(80))
        .unwrap();
    assert_eq!(empty.count(), 0);
    assert!(empty.extent().is_none());
    let empty = assembler.byte_initialized_eight_finish(empty).unwrap();
    assert_eq!(empty.count(), 0);
    assert!(empty.extent().is_none());
    assert!(empty.bounded_readback().is_none());
    let empty_read = independent_readback(&mut assembler, &empty, input_memory(), &[]);
    let mut claims = vec![empty_read];
    let cached_locals = assembler.locals;
    for count in [1, 2, 3, 8] {
        let words = vec![7; count];
        let prefix = raw_prefix(&mut assembler, &words);
        let read = assembler.byte_initialized_eight_finish(prefix).unwrap();
        claims.push(independent_readback(
            &mut assembler,
            &read,
            expected_memory(&words),
            &words,
        ));
        assert_eq!(assembler.initialized_eight_helper_builds, 1);
        assert_eq!(assembler.locals, cached_locals);
    }
    // Structural construction counts, not a claim about kernel normalization
    // or elapsed time. Each append contributes once irrespective of prefix size.
    assert_eq!(assembler.initialized_eight_appends, 14);
    drop(assembler);
    for claim in claims {
        replay(&scope, &claim, true);
    }

    let mut policy = limits();
    policy.max_list_items = 1;
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let prefix = raw_prefix(&mut assembler, &[7]);
    let before = prefix.memory().clone();
    let after = write(before.clone(), nat(88), nat(9));
    let admitted_appends = assembler.initialized_eight_appends;
    let rejected = assembler.byte_initialized_eight_append(
        prefix,
        nat(88),
        nat(9),
        after.clone(),
        InitializedEightAppendPremises {
            adjacent: conversion(
                constant("Nat"),
                nat(88),
                app("Nat.add", [nat(80), app("Nat.mul", [nat(8), nat(1)])]),
            ),
            written: conversion(
                constant("IRByteMemoryV1"),
                after,
                write(before, nat(88), nat(9)),
            ),
            bounded_word: bounded_word(nat(9), 9),
            extent: extent(80, 2),
        },
    );
    assert!(
        rejected.err().unwrap().contains("list budget"),
        "the accumulator must count its retained words"
    );
    assert_eq!(assembler.initialized_eight_appends, admitted_appends);

    let mut policy = limits();
    policy.max_operations = 1;
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    assembler.local(constant("Nat")).unwrap();
    assert!(
        assembler
            .byte_initialized_eight_empty(input_memory(), nat(80))
            .err()
            .unwrap()
            .contains("operation budget")
    );
}
