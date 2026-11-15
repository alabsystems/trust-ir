// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "source-value-operational")]
//! Actual retained producer module and checked source caller; model observations only.
use trust_ir::clean_boxed_u32::{
    Allocation, Fault, ReleaseEffect, RuntimeSources, UInt32Heap, encode,
};
use trust_ir::{Endianness, FuncId, Inst, Module, StructPassingPolicy, TargetInfo, Ty, ValueId};
use trust_ir_build::clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_ir_build::clean_u32_boxed_prefix::{
    PrefixError, PrefixProfile, PrefixStep, prepare_tagged_u32_boxed_prefix,
};
use trust_ir_build::core_execution::Limits;
use trust_ir_build::{
    CheckedSourceValueOperational, ModuleBuilder, check_u32_straight_line_source_value,
    check_u32_straight_line_source_value_with_validated_runtime_context,
    check_uint_source_value_equation,
};

const ORIGINAL: &[u8] =
    include_bytes!("fixtures/source_value_equations/boundActualEquation/module.bin");
fn fixture() -> Module {
    let module = trust_ir::binary::deserialize_module(ORIGINAL).unwrap();
    assert_eq!(
        trust_ir::binary::serialize_module(&module).unwrap(),
        ORIGINAL
    );
    assert_eq!((module.functions.len(), module.func_types.len()), (72, 73));
    assert_eq!(
        (
            module.proof_obligations.len(),
            module.proof_certificates.len()
        ),
        (1, 1)
    );
    module
}
fn subject(module: Module, run: impl FnOnce(&CheckedSourceValueOperational<'_>)) {
    macro_rules! data {
        ($file:literal) => {
            include_bytes!(concat!(
                "fixtures/source_value_equations/boundActualEquation/",
                $file
            ))
        };
    }
    fn expression(raw: &[u8]) -> Expr {
        trust_ir::proof::decode_clean_expr_v1(raw).unwrap()
    }
    fn name(raw: &[u8]) -> Name {
        let e = expression(raw);
        let trust_ir_build::clean_kernel::ExprKind::Const(n, levels) = e.kind() else {
            panic!("name carrier")
        };
        assert!(levels.is_empty());
        n.clone()
    }
    let mut environment = Environment::with_prelude();
    environment
        .add_decl(Declaration::Definition {
            name: name(data!("definition-0.name.bin")),
            level_params: vec![],
            type_: expression(data!("definition-0.type.bin")),
            value: expression(data!("definition-0.value.bin")),
            is_reducible: false,
        })
        .unwrap();
    let source = name(data!("definition-0.name.bin"));
    assert_eq!(
        environment.closure_digest(&source).unwrap().as_slice(),
        data!("source-closure-digest.bin")
    );
    let theorem = Declaration::Theorem {
        name: name(data!("theorem.name.bin")),
        level_params: vec![],
        type_: expression(data!("theorem.type.bin")),
        value: expression(data!("theorem.value.bin")),
    };
    // Real shared-reader success is mandatory, including the original metadata tables.
    let source =
        check_uint_source_value_equation(&module, FuncId(70), &environment, &source, &theorem)
            .unwrap();
    let addresses: Vec<_> = module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, 4096 + 8 * i as u64))
        .collect();
    let operational = check_u32_straight_line_source_value_with_validated_runtime_context(
        &source,
        &addresses,
        Limits {
            max_operations: 20000,
            max_locals: 4096,
            max_list_items: 4096,
            max_lookup_candidates: 1024,
            lookup_heartbeats: 1000000,
            lookup_cache_entries: 100000,
        },
    )
    .unwrap();
    assert!(core::ptr::eq(operational.source_value().module(), &module));
    assert!(core::ptr::eq(
        operational
            .retained_validation_report()
            .unwrap()
            .validated_module()
            .unwrap(),
        &module
    ));
    run(&operational);
}
fn runtime_sources() -> RuntimeSources<'static> {
    RuntimeSources {
        object_model: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/object_model.rs.txt"
        ),
        ctor_scalar: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/ctor_scalar.rs.txt"
        ),
        rc_core: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/rc_core.rs.txt"
        ),
        refcount: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/refcount.rs.txt"
        ),
        public_api: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/public_api.rs.txt"
        ),
    }
}
fn unrelated() -> Allocation {
    let mut bytes = 3u32.to_le_bytes().to_vec();
    bytes.extend([0, 0, 0, 4]);
    bytes.extend(99u32.to_le_bytes());
    Allocation {
        address: 0x1000,
        alignment: 8,
        bytes: bytes.into_iter().map(Some).collect(),
        live: true,
    }
}
fn heap() -> UInt32Heap {
    UInt32Heap::new(
        runtime_sources().bind().unwrap(),
        vec![unrelated()],
        [(0x1000, 1)].into(),
    )
    .unwrap()
}

#[test]
fn actual_retained_wrapper_prefix_preserves_identity_and_observes_each_node() {
    subject(fixture(), |source| {
        for (x, y) in [(3, 5), (0, 0), (u32::MAX, 3), (u32::MAX, u32::MAX)] {
            let binding = prepare_tagged_u32_boxed_prefix(source, FuncId(71)).unwrap();
            assert_eq!(
                binding.profile(),
                PrefixProfile::CleanUInt32Tagged64PrefixV1
            );
            assert!(core::ptr::eq(binding.scalar(), source));
            assert!(core::ptr::eq(
                binding.wrapper(),
                &source.source_value().module().functions[71]
            ));
            assert_eq!(
                (binding.unbox_id(), binding.box_id()),
                (FuncId(10), FuncId(4))
            );
            let initial = heap();
            let images = initial.allocations().clone();
            let credits = initial.caller_credits().clone();
            let mut machine = binding
                .start(initial, [encode(x).word(), encode(y).word()], 9)
                .unwrap();
            assert!(machine.handoff().unwrap().is_none());
            for (pc, input, result, value) in [(0, 0, 2, x), (1, 1, 3, y)] {
                let PrefixStep::Decoded {
                    site,
                    callee,
                    input: got_input,
                    result: got_result,
                    value: got_value,
                } = machine.step().unwrap()
                else {
                    panic!("actual unbox node")
                };
                assert_eq!(
                    (site.function, site.block.index(), site.node),
                    (FuncId(71), 0, pc)
                );
                assert_eq!(
                    (callee, got_input, got_result, got_value),
                    (FuncId(10), ValueId(input), ValueId(result), value)
                );
            }
            for slot in 0..2 {
                let PrefixStep::Released {
                    site,
                    operand,
                    slot: got_slot,
                    effect,
                } = machine.step().unwrap()
                else {
                    panic!("actual Release node")
                };
                assert_eq!(
                    (site.node, operand.index(), got_slot, effect),
                    (2 + slot, slot as u32, slot, ReleaseEffect::Tagged)
                );
                let snapshot = machine.snapshot().unwrap();
                assert_eq!(
                    snapshot.remaining_owned_slots,
                    if slot == 0 {
                        [false, true]
                    } else {
                        [false, false]
                    }
                );
                assert_eq!(snapshot.heap.allocations(), &images);
                assert_eq!(snapshot.heap.caller_credits(), &credits);
                assert!(!snapshot.heap.is_retired(snapshot.model_frame));
            }
            let handoff = machine.handoff().unwrap().unwrap();
            assert!(core::ptr::eq(handoff.source, source));
            assert!(core::ptr::eq(
                handoff.actual_call,
                &source.source_value().module().functions[71].blocks[0].body[4]
            ));
            assert_eq!(
                (
                    handoff.site.node,
                    handoff.callee,
                    handoff.operands,
                    handoff.remaining_budget
                ),
                (4, FuncId(70), [(ValueId(2), x), (ValueId(3), y)], 5)
            );
            // No scalar computation, box/Return or body license has been supplied.
            let before = machine.snapshot().unwrap();
            assert_eq!(machine.step(), Err(PrefixError::AtScalarHandoff));
            assert_eq!(machine.snapshot().unwrap(), before);
        }
        assert_eq!(
            trust_ir::binary::serialize_module(source.source_value().module()).unwrap(),
            ORIGINAL
        );
        assert!(
            trust_ir_build::codegen_license_errors(source.source_value().module())
                .iter()
                .any(|e| format!("{e:?}").contains("71"))
        );
    });
}

#[test]
fn prefix_budget_counts_only_observed_nodes_and_exhaustion_preserves_full_state() {
    subject(fixture(), |source| {
        for budget in 0..=4 {
            let mut machine = prepare_tagged_u32_boxed_prefix(source, FuncId(71))
                .unwrap()
                .start(heap(), [encode(7).word(), encode(11).word()], budget)
                .unwrap();
            for _ in 0..budget {
                assert!(!matches!(
                    machine.step().unwrap(),
                    PrefixStep::NoBudget { .. }
                ));
            }
            let before = machine.snapshot().unwrap();
            assert_eq!(
                (before.executed_nodes, before.remaining_budget),
                (budget as usize, 0)
            );
            assert_eq!(
                before.remaining_owned_slots,
                match budget {
                    0..=2 => [true, true],
                    3 => [false, true],
                    _ => [false, false],
                }
            );
            if budget < 4 {
                assert_eq!(
                    machine.step().unwrap(),
                    PrefixStep::NoBudget { next: before.next }
                );
                assert!(machine.handoff().unwrap().is_none());
            } else {
                assert_eq!(machine.step(), Err(PrefixError::AtScalarHandoff));
            }
            assert_eq!(machine.snapshot().unwrap(), before);
        }
    });
}

#[test]
fn tagged_domain_refusals_do_not_change_the_owned_model_or_admit_heap_arc() {
    subject(fixture(), |source| {
        for (words, expected) in [
            (
                [0x1000, encode(3).word()],
                PrefixError::OutsideTaggedDomain { input: 0 },
            ),
            (
                [encode(3).word(), 0],
                PrefixError::OutsideTaggedDomain { input: 1 },
            ),
            (
                [encode(3).word(), (1u64 << 33) | 1],
                PrefixError::Runtime(Fault::TaggedOutOfRange),
            ),
        ] {
            for budget in [0, 4] {
                let initial = heap();
                let before = initial.clone();
                let refusal = match prepare_tagged_u32_boxed_prefix(source, FuncId(71))
                    .unwrap()
                    .start(initial, words, budget)
                {
                    Ok(_) => panic!("outside tagged domain"),
                    Err(refusal) => refusal,
                };
                assert_eq!(refusal.error, expected);
                assert_eq!(refusal.heap, before);
            }
        }
    });
}

#[test]
fn genuinely_valid_changed_wrapper_graphs_are_refused_before_model_state_exists() {
    for case in 0..5 {
        let mut module = fixture();
        let body = &mut module.functions[71].blocks[0].body;
        match case {
            0 => body.swap(2, 3),
            1 => body[3].inst = Inst::Release { ptr: ValueId(0) },
            2 => {
                body.remove(2);
            }
            3 => {
                let Inst::Call { args, .. } = &mut body[4].inst else {
                    panic!()
                };
                args.swap(0, 1);
            }
            _ => {
                body[6].inst = Inst::Return {
                    values: vec![ValueId(0)],
                }
            }
        }
        // This callback is reached only AFTER genuine SourceEq and complete
        // full-context operational checking, never a forged receipt.
        subject(module, |source| {
            assert!(matches!(
                prepare_tagged_u32_boxed_prefix(source, FuncId(71)),
                Err(PrefixError::WrapperGraph)
            ));
        });
    }
}

#[test]
fn actual_descriptor_roles_are_not_selected_by_caller_digest_labels() {
    for (id, expected) in [
        (10, PrefixError::UnboxDescriptor),
        (4, PrefixError::BoxDescriptor),
    ] {
        let mut module = fixture();
        module.functions[id].name = "different_runtime_entry".into();
        subject(module, |source| {
            assert!(
                matches!(prepare_tagged_u32_boxed_prefix(source, FuncId(71)), Err(error) if error == expected)
            );
        });
    }
}

#[test]
fn an_ordinary_checked_receipt_does_not_substitute_for_retained_runtime_admission() {
    // Independently authored identity, not a pruned copy of the actual fixture.
    let mut builder = ModuleBuilder::new_with_target_info(
        "ordinary_identity",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let sig = builder.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let f = builder.declare_function("ordinary", sig);
    let mut body = builder.define_function(f).unwrap();
    let entry = body.create_block();
    let x = body.add_block_param(entry, Ty::U32);
    body.add_block_param(entry, Ty::U32);
    body.switch_to_block(entry);
    body.ret(vec![x]);
    body.build();
    let module = builder.build().unwrap();
    let uint = Expr::const_str("UInt32");
    let nat = Expr::const_str("Nat");
    let bind = |mut e, pi| {
        for _ in 0..2 {
            e = if pi {
                Expr::pi(BinderInfo::Default, uint.clone(), e)
            } else {
                Expr::lam(BinderInfo::Default, uint.clone(), e)
            };
        }
        e
    };
    let name = Name::from_string("PrefixAdmission.originalIdentity");
    let mut environment = Environment::with_prelude();
    environment
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
            value: bind(Expr::bvar(1), false),
            is_reducible: true,
        })
        .unwrap();
    let to_nat = |e| Expr::apps(Expr::const_str("UInt32.toNat"), [e]);
    let call = to_nat(Expr::apps(
        Expr::const_(name.clone(), vec![]),
        [Expr::bvar(1), Expr::bvar(0)],
    ));
    let theorem = Declaration::Theorem {
        name: Name::from_string("PrefixAdmission.untrustedEquation"),
        level_params: vec![],
        type_: bind(
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nat.clone(), call.clone(), to_nat(Expr::bvar(1))],
            ),
            true,
        ),
        value: bind(
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [nat, call],
            ),
            false,
        ),
    };
    let equation =
        check_uint_source_value_equation(&module, f, &environment, &name, &theorem).unwrap();
    let ordinary = check_u32_straight_line_source_value(
        &equation,
        &[(f, 4096)],
        Limits {
            max_operations: 20000,
            max_locals: 4096,
            max_list_items: 4096,
            max_lookup_candidates: 1024,
            lookup_heartbeats: 1000000,
            lookup_cache_entries: 100000,
        },
    )
    .unwrap();
    assert!(ordinary.retained_validation_report().is_none());
    assert!(matches!(
        prepare_tagged_u32_boxed_prefix(&ordinary, f),
        Err(PrefixError::RetainedSubject)
    ));
}
