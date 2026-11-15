// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Closed-template controls; candidate construction is not proof authority.
//! The oracle is the pre-change branch constructor, not a memory evaluator.

use super::*;

fn scoped_dispatch_functions(
    assembler: &mut Assembler<'_>,
    codec: &ByteFourCodec,
    input: &ByteLoadFour,
    store: bool,
) -> Result<WordDispatchFunctions> {
    let address = assembler.local(constant("Nat"))?;
    let shape = assembler.local(constant("IRByteLayoutV1"))?;
    let size = assembler.local(constant("Nat"))?;
    let pointer_success = address.lam(access_at(
        codec,
        input,
        shape.term().clone(),
        size.term().clone(),
        address.term().clone(),
        store,
    ));
    let pointer = option_branch(
        "Nat",
        fault("type_error", "not_ptr", input.memory.clone()),
        pointer_success.clone(),
        pointer_address(input.pointer.clone()),
    );
    let layout_success = shape.lam(choose(
        &constant("IRByteMemoryResultV1"),
        word_layout_condition(shape.term().clone(), size.term().clone()),
        pointer,
        fault("type_error", "width_bounded", input.memory.clone()),
    ));
    let layout = option_branch(
        "IRByteLayoutV1",
        fault("unmodelled", "width_bounded", input.memory.clone()),
        layout_success.clone(),
        app(
            "ir_byte_layout_v1",
            [codec.context.clone(), codec.ty.clone()],
        ),
    );
    Ok(WordDispatchFunctions {
        pointer: size.lam(shape.lam(pointer_success)),
        layout: size.lam(layout_success),
        size: size.lam(layout),
    })
}

fn function_type(domains: &[&str]) -> Expr {
    domains
        .iter()
        .rev()
        .fold(constant("IRByteMemoryResultV1"), |body, name| {
            Expr::pi(clean_kernel::BinderInfo::Default, constant(name), body)
        })
}

fn replay_closed(proof: PendingEquality) {
    let term = proof.term().clone();
    let claim = proof.proposition();
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap(),
    )
    .unwrap();
    for term in [&term, &decoded] {
        let mut checker = TypeChecker::new(environment());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        // New small template judgments retain the ordinary default replay
        // heartbeat/cache policy, not the older fixture's explicit5M lane.
        checker
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        checker.check_type(term, &claim).unwrap();
        assert!(!checker.heartbeat_spent());
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        let audit = environment().audit_certification(&claim, term);
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
    }
}

#[test]
fn closed_word_templates_match_scoped_oracles_under_one_neutral_telescope() {
    let f = fixture_word(8, false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut codec = codec_for(&mut assembler, &model, f.ty, 8, 7, TestApi::Word);
    let parameters = [
        "IRByteContextV1",
        "IRTy",
        "IRScalar",
        "IRScalar",
        "Nat",
        "IRByteMemoryV1",
    ]
    .map(|name| assembler.local(constant(name)).unwrap());
    codec.context = parameters[0].term().clone();
    codec.ty = parameters[1].term().clone();
    codec.value = parameters[2].term().clone();
    let input = ByteLoadFour {
        pointer: parameters[3].term().clone(),
        address: nat(80),
        requested_align: parameters[4].term().clone(),
        memory: parameters[5].term().clone(),
    };
    let mut proofs = Vec::new();
    for store in [false, true] {
        let before = (assembler.operations(), assembler.locals);
        let old = scoped_dispatch_functions(&mut assembler, &codec, &input, store).unwrap();
        assert_eq!(
            (
                assembler.operations() - before.0,
                assembler.locals - before.1
            ),
            (3, 3)
        );
        let new = closed_word_dispatch_functions(store);
        let domains = [
            vec![
                "IRByteContextV1",
                "IRTy",
                "IRScalar",
                "IRScalar",
                "Nat",
                "IRByteMemoryV1",
                "Nat",
                "IRByteLayoutV1",
                "Nat",
            ],
            vec![
                "IRByteContextV1",
                "IRTy",
                "IRScalar",
                "IRScalar",
                "Nat",
                "IRByteMemoryV1",
                "Nat",
                "IRByteLayoutV1",
            ],
            vec![
                "IRByteContextV1",
                "IRTy",
                "IRScalar",
                "IRScalar",
                "Nat",
                "IRByteMemoryV1",
                "Nat",
            ],
        ];
        for ((old, new), domains) in [old.pointer, old.layout, old.size]
            .into_iter()
            .zip([new.pointer, new.layout, new.size])
            .zip(domains)
        {
            let closed = parameters
                .iter()
                .rev()
                .fold(old, |body, parameter| parameter.lam(body));
            let closed = assembler.local_scope().close(&closed).unwrap();
            assert_eq!(closed, new, "only closed binder construction may change");
            let ty = function_type(&domains);
            proofs.push(PendingEquality::candidate(
                ty.clone(),
                new,
                closed.clone(),
                refl(&ty, closed),
            ));
        }
    }
    for count in [1u64, 2, 4] {
        let memory = assembler.local(constant("IRByteMemoryV1")).unwrap();
        let address = assembler.local(constant("Nat")).unwrap();
        let word = assembler.local(constant("Nat")).unwrap();
        let old = word.lam(store_word_branch_at(
            memory.term().clone(),
            address.term().clone(),
            word.term().clone(),
            count,
        ));
        let old = memory.lam(address.lam(old));
        let old = assembler.local_scope().close(&old).unwrap();
        let new = closed_store_word_function(count);
        assert_eq!(old, new);
        let ty = function_type(&["IRByteMemoryV1", "Nat", "Nat"]);
        proofs.push(PendingEquality::candidate(
            ty.clone(),
            new,
            old.clone(),
            refl(&ty, old),
        ));
    }
    drop(assembler);
    for proof in proofs {
        replay_closed(proof);
    }
}

#[test]
fn closed_word_templates_keep_caller_arguments_outside_binders() {
    let f = fixture_word(8, false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut codec = codec_for(&mut assembler, &model, f.ty, 8, 7, TestApi::Word);
    codec.context = Expr::bvar(5);
    codec.ty = Expr::bvar(4);
    codec.value = Expr::bvar(3);
    let input = ByteLoadFour {
        pointer: Expr::bvar(2),
        address: nat(80),
        requested_align: Expr::bvar(1),
        memory: Expr::bvar(0),
    };
    let expected_arguments = WordDispatchInput::actual(&codec, &input).arguments();
    let mut proofs = Vec::new();
    for store in [false, true] {
        let before = (assembler.operations(), assembler.locals);
        let applied = word_dispatch_functions(&mut assembler, &codec, &input, store).unwrap();
        assert_eq!(
            (
                assembler.operations() - before.0,
                assembler.locals - before.1
            ),
            (3, 0)
        );
        let templates = closed_word_dispatch_functions(store);
        for ((applied, template), extra) in [applied.pointer, applied.layout, applied.size]
            .into_iter()
            .zip([templates.pointer, templates.layout, templates.size])
            .zip([
                vec!["Nat", "IRByteLayoutV1", "Nat"],
                vec!["Nat", "IRByteLayoutV1"],
                vec!["Nat"],
            ])
        {
            assert_eq!(applied.get_app_fn(), &template);
            assert!(!template.has_fvar_quick() && !template.has_loose_bvars());
            assert_eq!(
                applied
                    .get_app_args()
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>(),
                expected_arguments
            );
            let closed = close_word_dispatch(applied);
            let mut domains = vec![
                "IRByteContextV1",
                "IRTy",
                "IRScalar",
                "IRScalar",
                "Nat",
                "IRByteMemoryV1",
            ];
            domains.extend(extra);
            let ty = function_type(&domains);
            proofs.push(PendingEquality::candidate(
                ty.clone(),
                closed,
                template.clone(),
                refl(&ty, template),
            ));
        }
    }
    drop(assembler);
    for proof in proofs {
        replay_closed(proof);
    }
}

#[test]
fn closed_word_templates_repeat_full_store_without_cache_and_check_unused_bad_evidence() {
    for bits in [8, 16, 32] {
        let f = fixture_word(bits, false, false);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let codec = codec_for(&mut assembler, &model, f.ty, bits, 7, TestApi::Word);
        let input = load_input_word(app("IRScalar.ptr_", [nat(80)]), 80, memory(0), f.bytes);
        let premises = ByteStoreWordPremises {
            pointer: pointer(&input),
            accessible: accessible(&codec, &input),
        };
        let mut proofs = Vec::new();
        for _ in 0..2 {
            let before = (
                assembler.operations(),
                assembler.locals,
                assembler.local_scope().allocated(),
            );
            let stored = public_store(&mut assembler, &codec, &input, premises.clone()).unwrap();
            assert_eq!(
                (
                    assembler.operations() - before.0,
                    assembler.locals - before.1,
                    assembler.local_scope().allocated() - before.2
                ),
                (13 + f.bytes as usize, 0, 0)
            );
            proofs.extend([
                stored.evaluated,
                stored.allocations,
                stored.cursor,
                stored.raw_read,
                stored.typed_readback,
            ]);
        }
        let mut negatives = Vec::new();
        for field in 0..8 {
            let mut codec = codec.clone();
            let mut premises = premises.clone();
            let term = if field == 7 {
                &mut codec.bounded.term
            } else {
                let equality = match field {
                    0 => &mut codec.lane,
                    1 => &mut codec.layout_found,
                    2 => &mut premises.pointer,
                    3 => &mut codec.encoded,
                    4 => &mut codec.fits,
                    5 => &mut premises.accessible,
                    6 => &mut codec.decoded,
                    _ => unreachable!(),
                };
                &mut equality.term
            };
            // The bad value is unused by the body but MUST still be checked.
            *term = Expr::let_named(
                Name::anon(),
                constant("Nat"),
                constant("Bool.true"),
                term.lift(1),
                false,
            );
            let stored = public_store(&mut assembler, &codec, &input, premises).unwrap();
            negatives.push(if field == 6 {
                stored.typed_readback
            } else {
                stored.evaluated
            });
        }
        drop(assembler);
        for proof in proofs {
            replay_both(&scope, &proof, true);
        }
        for proof in negatives {
            replay_both(&scope, &proof, false);
        }
        // Partial operation exhaustion remains charged and cannot publish a
        // cache (none exists) or allocate helper locals on a later attempt.
        for cap in [1, 2] {
            let mut partial_limits = limits();
            partial_limits.max_operations = cap;
            let mut partial = Assembler::new(&mut scope, partial_limits).unwrap();
            assert_eq!(
                public_store(&mut partial, &codec, &input, premises.clone())
                    .err()
                    .unwrap(),
                "execution construction operation budget exceeded"
            );
            assert_eq!((partial.operations(), partial.locals), (cap, 0));
            assert!(public_store(&mut partial, &codec, &input, premises.clone()).is_err());
            assert_eq!((partial.operations(), partial.locals), (cap, 0));
            partial.operations = usize::MAX;
            assert_eq!(
                public_store(&mut partial, &codec, &input, premises.clone())
                    .err()
                    .unwrap(),
                "operation counter overflow"
            );
            assert_eq!((partial.operations(), partial.locals), (usize::MAX, 0));
        }
        let mut global_scope = Scope::with_limits(crate::scoped_local::LocalScopeLimits {
            max_locals: 1,
            ..Default::default()
        });
        let inherited = global_scope.try_local(constant("Nat")).unwrap();
        let mut global = Assembler::new(&mut global_scope, limits()).unwrap();
        let stored = public_store(&mut global, &codec, &input, premises.clone()).unwrap();
        assert_eq!((global.locals, global.local_scope().allocated()), (0, 1));
        let spent = global.operations();
        assert_eq!(
            global.local(constant("Nat")).err().unwrap(),
            "named local allocation limit 1 exceeded"
        );
        assert_eq!(
            (
                global.operations(),
                global.locals,
                global.local_scope().allocated()
            ),
            (spent + 1, 0, 1)
        );
        drop(global);
        drop(inherited);
        replay_both(&global_scope, &stored.evaluated, true);
        replay_both(&global_scope, &stored.typed_readback, true);
    }
}
