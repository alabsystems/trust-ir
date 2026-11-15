// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Independent symbolic and genuinely fetched Bool ZExt consumers.
//! These candidates are not source, native ABI or checked Rust authority.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{CastOp, Endianness, Module, StructPassingPolicy, TargetInfo};

fn destinations() -> [Ty; 10] {
    [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::U64,
        Ty::I128,
        Ty::U128,
    ]
}

fn destination(ty: &Ty) -> Expr {
    let (constructor, width) = match ty {
        Ty::I8 => ("IRTy.int_", 8),
        Ty::U8 => ("IRTy.uint_", 8),
        Ty::I16 => ("IRTy.int_", 16),
        Ty::U16 => ("IRTy.uint_", 16),
        Ty::I32 => ("IRTy.int_", 32),
        Ty::U32 => ("IRTy.uint_", 32),
        Ty::I64 => ("IRTy.int_", 64),
        Ty::U64 => ("IRTy.uint_", 64),
        Ty::I128 => ("IRTy.int_", 128),
        Ty::U128 => ("IRTy.uint_", 128),
        _ => panic!("independent nominal integer test type"),
    };
    Expr::apps(Expr::const_str(constructor), [Expr::nat_lit(width)])
}

fn raw(flag: Expr, swapped: bool) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, constant("Bool"), constant("Nat")),
            nat(u64::from(swapped)),
            nat(u64::from(!swapped)),
            flag,
        ],
    )
}

fn scalar(flag: Expr) -> Expr {
    app("IRScalar.int_", [raw(flag, false)])
}

fn eval(context: Expr, operation: &str, ty: Expr, flag: Expr) -> Expr {
    app(
        "ir_byte_cast_eval_v1",
        [
            context,
            constant(operation),
            constant("IRTy.bool_"),
            ty,
            app("IRScalar.bool_", [flag]),
        ],
    )
}

fn eval_claim(context: Expr, ty: Expr, flag: Expr) -> Expr {
    eq(
        &constant("IRStepResult"),
        eval(context, "IRCastOp.zext", ty, flag.clone()),
        app("IRStepResult.value", [scalar(flag)]),
    )
}

fn fits_claim(context: Expr, ty: Expr, flag: Expr) -> Expr {
    eq(
        &constant("Bool"),
        app("ir_byte_value_matches_v1", [context, ty, scalar(flag)]),
        constant("Bool.true"),
    )
}

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .expect("actual checked ByteV1 owner")
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut tc = TypeChecker::new(environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    assert_eq!(tc.heartbeat_limit(), 2_000_000);
    tc
}

fn replay(claim: &Expr, proof: &Expr, accepted: bool) {
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    checker().check_type(claim, &Expr::prop()).unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(claim).unwrap(),
    )
    .unwrap();
    let decoded_proof = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(proof).unwrap(),
    )
    .unwrap();
    assert_eq!(&decoded_claim, claim);
    assert_eq!(&decoded_proof, proof);
    for (goal, term) in [(claim, proof), (&decoded_claim, &decoded_proof)] {
        let tc = checker();
        let result = tc.check_type(term, goal);
        assert!(
            !tc.heartbeat_spent(),
            "resource stop is not a verdict: {result:?}"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            result.unwrap();
            let audit = environment().audit_certification(goal, term);
            assert!(audit.is_certified(), "{audit:#?}");
            for name in &audit.dependencies {
                assert!(environment().axiom_deps(name).unwrap().is_empty());
                assert!(
                    environment()
                        .foundational_axiom_deps(name)
                        .unwrap()
                        .is_empty()
                );
                assert!(environment().trust_marker_deps(name).unwrap().is_empty());
            }
        } else {
            assert!(
                matches!(result, Err(KernelTypeError::TypeMismatch { .. })),
                "{result:?}"
            );
        }
    }
}

fn limits(operations: usize) -> Limits {
    Limits {
        max_operations: operations,
        max_locals: 8,
        max_list_items: 8,
        max_lookup_candidates: 8,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 100_000,
    }
}

fn derive(ty: &Ty, context: Expr, flag: Expr) -> ByteBoolZext {
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits(1)).unwrap();
    let candidate = a.byte_bool_zext(context, ty, flag).unwrap();
    assert_eq!(a.operations(), 1);
    assert_eq!(a.locals, 0);
    assert_eq!(a.local_scope().allocated(), 0);
    assert!(a.cons_congruence.is_none() && a.run_one_candidate.is_none());
    candidate
}

fn forall_context_flag(claim: Expr) -> Expr {
    Expr::pi(
        BinderInfo::Default,
        constant("IRByteContextV1"),
        Expr::pi(BinderInfo::Default, constant("Bool"), claim),
    )
}

fn lambda_context_flag(proof: Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        constant("IRByteContextV1"),
        Expr::lam(BinderInfo::Default, constant("Bool"), proof),
    )
}

#[test]
fn bool_zext_preserves_exact_nominal_metadata_one_charge_and_closed_argument_placement() {
    for ty in destinations() {
        for (ctx, flag) in [
            (constant("caller_context"), constant("caller_flag")),
            (Expr::bvar(4), Expr::bvar(2)),
        ] {
            let candidate = derive(&ty, ctx.clone(), flag.clone());
            assert_eq!(candidate.word, raw(flag.clone(), false));
            assert_eq!(candidate.value, scalar(flag.clone()));
            assert_eq!(
                candidate.evaluated.proposition(),
                eval_claim(ctx.clone(), destination(&ty), flag.clone())
            );
            assert_eq!(
                candidate.fits.proposition(),
                fits_claim(ctx.clone(), destination(&ty), flag.clone())
            );
            for proof in [candidate.evaluated.term(), candidate.fits.term()] {
                assert!(
                    !proof.get_app_fn().has_fvar_quick() && !proof.get_app_fn().has_loose_bvars()
                );
                assert_eq!(proof.get_app_args().as_slice(), &[&ctx, &flag]);
            }
        }
    }
}

#[test]
fn bool_zext_all_nominal_widths_replay_symbolic_and_both_inhabited_cases_original_and_dag() {
    for ty in destinations() {
        let ctx = Expr::bvar(1);
        let flag = Expr::bvar(0);
        let candidate = derive(&ty, ctx.clone(), flag.clone());
        for (claim, proof) in [
            (
                eval_claim(ctx.clone(), destination(&ty), flag.clone()),
                candidate.evaluated.term(),
            ),
            (
                fits_claim(ctx, destination(&ty), flag),
                candidate.fits.term(),
            ),
        ] {
            replay(
                &forall_context_flag(claim),
                &lambda_context_flag(proof.clone()),
                true,
            );
        }
        for boolean in ["Bool.false", "Bool.true"] {
            let ctx = Expr::bvar(0);
            let flag = constant(boolean);
            let candidate = derive(&ty, ctx.clone(), flag.clone());
            for (claim, proof) in [
                (
                    eval_claim(ctx.clone(), destination(&ty), flag.clone()),
                    candidate.evaluated.term(),
                ),
                (
                    fits_claim(ctx, destination(&ty), flag),
                    candidate.fits.term(),
                ),
            ] {
                replay(
                    &Expr::pi(BinderInfo::Default, constant("IRByteContextV1"), claim),
                    &Expr::lam(
                        BinderInfo::Default,
                        constant("IRByteContextV1"),
                        proof.clone(),
                    ),
                    true,
                );
            }
        }
    }
}

#[test]
fn bool_zext_caller_owned_free_and_outer_bound_variables_are_not_recaptured() {
    let mut scope = Scope::new();
    let ctx = scope.try_local(constant("IRByteContextV1")).unwrap();
    let flag = scope.try_local(constant("Bool")).unwrap();
    let mut a = Assembler::new(&mut scope, limits(1)).unwrap();
    let candidate = a
        .byte_bool_zext(ctx.term().clone(), &Ty::U128, flag.term().clone())
        .unwrap();
    assert_eq!(a.local_scope().allocated(), 2);
    assert_eq!(a.locals, 0);
    for (claim, proof) in [
        (
            eval_claim(Expr::bvar(1), destination(&Ty::U128), Expr::bvar(0)),
            candidate.evaluated.term(),
        ),
        (
            fits_claim(Expr::bvar(1), destination(&Ty::U128), Expr::bvar(0)),
            candidate.fits.term(),
        ),
    ] {
        let term = a
            .local_scope()
            .close(&ctx.lam(flag.lam(proof.clone())))
            .unwrap();
        replay(&forall_context_flag(claim), &term, true);
    }
}

#[test]
fn bool_zext_false_opcode_word_width_and_forged_fit_fail_semantically_without_budget_stops() {
    let ctx = Expr::bvar(1);
    let flag = Expr::bvar(0);
    let candidate = derive(&Ty::I64, ctx.clone(), flag.clone());
    let wrong = [
        eq(
            &constant("IRStepResult"),
            eval(
                ctx.clone(),
                "IRCastOp.sext",
                destination(&Ty::I64),
                flag.clone(),
            ),
            app("IRStepResult.value", [scalar(flag.clone())]),
        ),
        eq(
            &constant("IRStepResult"),
            eval(
                ctx.clone(),
                "IRCastOp.zext",
                destination(&Ty::I64),
                flag.clone(),
            ),
            app(
                "IRStepResult.value",
                [app("IRScalar.int_", [raw(flag.clone(), true)])],
            ),
        ),
        eq(
            &constant("IRStepResult"),
            eval(
                ctx.clone(),
                "IRCastOp.zext",
                app("IRTy.uint_", [nat(0)]),
                flag.clone(),
            ),
            app("IRStepResult.value", [scalar(flag.clone())]),
        ),
        eq(
            &constant("IRStepResult"),
            eval(
                ctx.clone(),
                "IRCastOp.zext",
                app("IRTy.int_", [nat(129)]),
                flag.clone(),
            ),
            app("IRStepResult.value", [scalar(flag.clone())]),
        ),
        eq(
            &constant("IRStepResult"),
            eval(
                ctx.clone(),
                "IRCastOp.zext",
                constant("IRTy.ptr_"),
                flag.clone(),
            ),
            app("IRStepResult.value", [scalar(flag.clone())]),
        ),
    ];
    for claim in wrong {
        replay(
            &forall_context_flag(claim),
            &lambda_context_flag(candidate.evaluated.term().clone()),
            false,
        );
    }
    let false_fit = fits_claim(ctx, app("IRTy.uint_", [nat(0)]), flag);
    replay(
        &forall_context_flag(false_fit),
        &lambda_context_flag(candidate.fits.term().clone()),
        false,
    );
    // Correct metadata cannot turn this unrelated equality proof into Fits.
    let forged = refl(&constant("Nat"), nat(0));
    replay(
        &forall_context_flag(fits_claim(
            Expr::bvar(1),
            destination(&Ty::I64),
            Expr::bvar(0),
        )),
        &lambda_context_flag(forged),
        false,
    );
    // An ill-typed flag goes in the proof only; the independent claim is valid.
    let non_bool = derive(&Ty::I64, Expr::bvar(0), nat(1));
    let true_claim = eval_claim(Expr::bvar(0), destination(&Ty::I64), constant("Bool.true"));
    replay(
        &Expr::pi(BinderInfo::Default, constant("IRByteContextV1"), true_claim),
        &Expr::lam(
            BinderInfo::Default,
            constant("IRByteContextV1"),
            non_bool.evaluated.term().clone(),
        ),
        false,
    );
}

fn providers() -> Expr {
    [
        constant("Nat"),
        app("IRList", [constant("IRScalar")]),
        constant("IRByteMemoryV1"),
        constant("Nat"),
    ]
    .into_iter()
    .rev()
    .fold(
        app(
            "IRByteImportResultV1.mk",
            [
                constant("Nat"),
                app("IROutcome.stuck", [constant("IRFault.no_func")]),
                Expr::bvar(1),
                Expr::bvar(0),
            ],
        ),
        |body, ty| Expr::lam(BinderInfo::Default, ty, body),
    )
}

struct Fixture {
    module: Module,
    function: FuncId,
    block: BlockId,
    operand: ValueId,
    alternate: ValueId,
    result: ValueId,
}

fn fixture(ty: Ty) -> Fixture {
    let mut builder = ModuleBuilder::new_with_target_info(
        "symbolic_bool_zext",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::Bool, Ty::Bool], vec![ty.clone()]);
    let function = builder.declare_function("extend", signature);
    let (block, operand, alternate, result);
    {
        let mut body = builder.define_function(function).unwrap();
        block = body.create_block();
        operand = body.add_block_param(block, Ty::Bool);
        alternate = body.add_block_param(block, Ty::Bool);
        body.switch_to_block(block);
        result = body.cast(CastOp::ZExt, Ty::Bool, ty, operand);
        body.ret(vec![result]);
        body.build();
    }
    let module = builder.build().unwrap();
    assert!(crate::validate_module(&module).is_empty());
    Fixture {
        module,
        function,
        block,
        operand,
        alternate,
        result,
    }
}

fn world(host: u64) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            app(
                "IRByteMemoryV1.mk",
                [
                    list(
                        "IRByteAllocationV1",
                        &[
                            app(
                                "IRByteAllocationV1.mk",
                                [nat(16), nat(16), nat(8), constant("Bool.true")],
                            ),
                            app(
                                "IRByteAllocationV1.mk",
                                [nat(80), nat(8), nat(0), constant("Bool.true")],
                            ),
                        ],
                    ),
                    Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173))),
                    nat(192),
                ],
            ),
            nat(host),
            list("Nat", &[nat(8)]),
            nat(9),
        ],
    )
}

fn current(f: &Fixture, flag: Expr) -> Current {
    Current {
        frame: app(
            "IRFrame.mk",
            [
                nat(u64::from(f.function.index())),
                nat(u64::from(f.block.index())),
                nat(0),
                list(
                    "IRBinding",
                    &[
                        app(
                            "IRBinding.mk",
                            [
                                nat(u64::from(f.operand.index())),
                                app("IRScalar.bool_", [flag]),
                            ],
                        ),
                        app(
                            "IRBinding.mk",
                            [
                                nat(u64::from(f.alternate.index())),
                                app("IRScalar.bool_", [constant("Bool.false")]),
                            ],
                        ),
                    ],
                ),
                list("Nat", &[]),
            ],
        ),
        tail: list("IRFrame", &[]),
        legacy_memory: list("IRMemSlot", &[]),
        legacy_cursor: nat(0),
        world: world(37),
    }
}

fn after(f: &Fixture, before: &Current, flag: Expr, pc: u64, host: u64) -> Current {
    let fields = before.frame.get_app_args();
    Current {
        frame: app(
            "IRFrame.mk",
            [
                (*fields[0]).clone(),
                (*fields[1]).clone(),
                nat(pc),
                app(
                    "IRList.cons",
                    [
                        constant("IRBinding"),
                        app(
                            "IRBinding.mk",
                            [nat(u64::from(f.result.index())), scalar(flag)],
                        ),
                        (*fields[3]).clone(),
                    ],
                ),
                (*fields[4]).clone(),
            ],
        ),
        world: world(host),
        ..before.clone()
    }
}

#[test]
fn bool_zext_actual_fetched_symbolic_steps_preserve_ssa_destination_pc_and_entire_world() {
    for ty in destinations() {
        let f = fixture(ty.clone());
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits(1_000)).unwrap();
        let site = catalog
            .fetch(Coordinate {
                function: f.function,
                block: f.block,
                instruction: 0,
            })
            .unwrap();
        let flag = Expr::bvar(0);
        let before = current(&f, flag.clone());
        let expected = after(&f, &before, flag.clone(), 1, 37);
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits(1_000)).unwrap();
        let candidate = a
            .byte_bool_zext(model.context().clone(), &ty, flag.clone())
            .unwrap();
        let checks = site
            .scalar_checks(&model, &before, candidate.value.clone())
            .unwrap();
        let evaluated = a
            .ascribe_endpoints(
                candidate.evaluated,
                checks.evaluation,
                app("IRStepResult.value", [candidate.value.clone()]),
            )
            .unwrap();
        let result = a
            .congruence(candidate.fits, constant("Bool"), |fits| {
                app(
                    "Bool.and",
                    [
                        constant("Bool.true"),
                        app("Bool.and", [fits, constant("Bool.true")]),
                    ],
                )
            })
            .unwrap();
        let result = a
            .ascribe_endpoints(result, checks.result, constant("Bool.true"))
            .unwrap();
        let operands = a
            .conversion(constant("Bool"), checks.operands, constant("Bool.true"))
            .unwrap();
        let valid = a
            .conversion(
                constant("Bool"),
                before.valid(&model),
                constant("Bool.true"),
            )
            .unwrap();
        let premises = ScalarPremises {
            evaluated,
            operands,
            result,
            before: valid,
        };
        // Different ADMITTED destination widths still compute the same 0/1;
        // these are exact fetched-metadata refusals, not false arithmetic laws.
        for field in 0..5 {
            let mut wrong_site = site.clone();
            let mut fields = site
                .instruction
                .get_app_args()
                .iter()
                .map(|field| (**field).clone())
                .collect::<Vec<_>>();
            match field {
                0 => fields[0] = constant("IRCastOp.sext"),
                1 => fields[1] = app("IRTy.uint_", [nat(8)]),
                2 => fields[2] = destination(if ty == Ty::U8 { &Ty::U16 } else { &Ty::U8 }),
                3 => fields[3] = nat(u64::from(f.alternate.index())),
                _ => wrong_site.results = list("Nat", &[nat(u64::from(f.result.index()) + 1)]),
            }
            wrong_site.instruction = app("IRInst.cast", fields);
            assert!(
                wrong_site
                    .scalar_value(
                        &mut a,
                        &model,
                        &before,
                        candidate.value.clone(),
                        premises.clone()
                    )
                    .is_err()
            );
        }
        let mut foreign_site = site.clone();
        foreign_site.context = constant("foreign_context");
        assert!(
            foreign_site
                .scalar_value(
                    &mut a,
                    &model,
                    &before,
                    candidate.value.clone(),
                    premises.clone()
                )
                .is_err()
        );
        let transfer = site
            .scalar_value(&mut a, &model, &before, candidate.value, premises)
            .unwrap();
        for (claim, proof) in [
            (
                eq(
                    &model.config_type(),
                    model.step(before.running(&model)),
                    expected.running(&model),
                ),
                transfer.step().term(),
            ),
            (
                eq(
                    &model.config_type(),
                    model.run(&NatTerm::literal(1), before.running(&model)),
                    expected.running(&model),
                ),
                transfer.run().equality().term(),
            ),
            (
                eq(
                    &constant("Bool"),
                    expected.valid(&model),
                    constant("Bool.true"),
                ),
                transfer.valid().term(),
            ),
        ] {
            let proof = a
                .local_scope()
                .close(&Expr::lam(
                    BinderInfo::Default,
                    constant("Bool"),
                    proof.clone(),
                ))
                .unwrap();
            replay(
                &Expr::pi(BinderInfo::Default, constant("Bool"), claim),
                &proof,
                true,
            );
        }
        assert_eq!(&transfer.current().world, &before.world);
        assert_eq!(&transfer.current().tail, &before.tail);
        assert_eq!(&transfer.current().legacy_memory, &before.legacy_memory);
        assert_eq!(&transfer.current().legacy_cursor, &before.legacy_cursor);
        for changed in [
            after(&f, &before, flag.clone(), 2, 37),
            after(&f, &before, flag.clone(), 1, 38),
            after(&f, &before, constant("Bool.false"), 1, 37),
        ] {
            let claim = eq(
                &model.config_type(),
                model.step(before.running(&model)),
                changed.running(&model),
            );
            let proof = a
                .local_scope()
                .close(&Expr::lam(
                    BinderInfo::Default,
                    constant("Bool"),
                    transfer.step().term().clone(),
                ))
                .unwrap();
            replay(
                &Expr::pi(BinderInfo::Default, constant("Bool"), claim),
                &proof,
                false,
            );
        }
        let wrong_fuel = eq(
            &model.config_type(),
            model.run(&NatTerm::literal(2), before.running(&model)),
            expected.running(&model),
        );
        let proof = a
            .local_scope()
            .close(&Expr::lam(
                BinderInfo::Default,
                constant("Bool"),
                transfer.run().equality().term().clone(),
            ))
            .unwrap();
        replay(
            &Expr::pi(BinderInfo::Default, constant("Bool"), wrong_fuel),
            &proof,
            false,
        );
    }
}

#[test]
fn bool_zext_invalid_destinations_and_spent_operation_overflow_fail_without_local_or_cache_changes()
{
    let mut zero_scope = Scope::new();
    assert_eq!(
        Assembler::new(&mut zero_scope, limits(0)).err().as_deref(),
        Some("execution construction limits must be nonzero")
    );
    assert_eq!(zero_scope.allocated(), 0);
    for ty in [Ty::Bool, Ty::Ptr, Ty::F32, Ty::Usize, Ty::Isize] {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits(1)).unwrap();
        assert_eq!(
            a.byte_bool_zext(constant("ctx"), &ty, constant("flag"))
                .err()
                .as_deref(),
            Some("Boolean ZExt requires a nominal I/U8..128 destination")
        );
        assert_eq!(a.operations(), 1);
        assert_eq!(
            a.byte_bool_zext(constant("ctx"), &Ty::U8, constant("flag"))
                .err()
                .as_deref(),
            Some("execution construction operation budget exceeded")
        );
        assert_eq!(a.operations(), 1);
        assert_eq!(a.locals, 0);
        assert_eq!(a.local_scope().allocated(), 0);
    }
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits(1)).unwrap();
    a.operations = usize::MAX;
    assert_eq!(
        a.byte_bool_zext(constant("ctx"), &Ty::I64, constant("flag"))
            .err()
            .as_deref(),
        Some("operation counter overflow")
    );
    assert_eq!(a.operations(), usize::MAX);
    assert_eq!(a.locals, 0);
    assert_eq!(a.local_scope().allocated(), 0);
    assert!(a.cons_congruence.is_none() && a.run_one_candidate.is_none());
}
