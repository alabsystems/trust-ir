// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Ordinary authored Core consumes the shared pointer cast producer, including
//! its real fetched operand and whole scalar-step World. No TLA environment,
//! callee summary, native permission or replacement evaluator participates.

use super::*;
use clean_kernel::env::ConstantKind;

fn replay(claim: &Expr, proof: &Expr, accepted: bool) {
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    let decode = |term| {
        trust_ir::proof::decode_clean_expr_dag_v2(
            &trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap(),
        )
        .unwrap()
    };
    let decoded_claim = decode(claim);
    let decoded_proof = decode(proof);
    assert_eq!(&decoded_claim, claim);
    assert_eq!(&decoded_proof, proof);
    for (claim, proof) in [(claim, proof), (&decoded_claim, &decoded_proof)] {
        let tc = checker(); // The maintained fetched-cast profile, unchanged.
        tc.check_type(claim, &Expr::prop()).unwrap();
        let result = tc.check_type(proof, claim);
        assert!(
            !tc.heartbeat_spent(),
            "resource stop is not rejection: {result:?}"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            result.unwrap();
            let audit = environment().audit_certification(claim, proof);
            assert!(audit.is_certified(), "{audit:#?}");
            for name in &audit.dependencies {
                assert_ne!(
                    environment().get_const(name).unwrap().kind,
                    ConstantKind::Axiom
                );
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

fn bound(word: Expr, term: Expr) -> PendingProof {
    PendingProof::candidate(app("Nat.lt", [word, constant("ir_byte_limit_v1")]), term)
}

fn literal_bound(word: u64) -> PendingProof {
    bound(
        nat(word),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(word)]), nat(u64::MAX - word)],
        ),
    )
}

fn canonical_pointer(
    a: &mut Assembler<'_>,
    context: Expr,
    word: Expr,
    bounded: &PendingProof,
) -> BytePointerWord {
    let guard = app("ir_nat_ltb", [word.clone(), app("ir_nat_pow2", [nat(64)])]);
    a.byte_pointer_word(
        context,
        word.clone(),
        PendingEquality::candidate(
            constant("Bool"),
            guard,
            constant("Bool.true"),
            app(
                "ir_byte_ltb_of_lt_v1",
                [word, app("ir_nat_pow2", [nat(64)]), bounded.term().clone()],
            ),
        ),
    )
    .unwrap()
}

fn close(scope: &Scope, parameters: &[Local], term: Expr, claim: bool) -> Expr {
    let term = parameters.iter().rev().fold(term, |body, local| {
        if claim {
            local.pi(body)
        } else {
            local.lam(body)
        }
    });
    scope.close(&term).unwrap()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Change {
    None,
    Operand,
    InputFit,
    Recovery,
    Address,
    Bound,
    NullCarrier,
    Output,
    Pc,
    Fuel,
    World,
}

fn fetched(destination: Ty, numeral: Option<u64>, change: Change) -> (Expr, Expr) {
    let f = fixture(CastOp::PtrToInt, Ty::Ptr, destination.clone());
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let mut scope = Scope::new();
    let mut parameters = Vec::new();
    let (word, bounded) = if let Some(n) = numeral {
        (nat(n), literal_bound(n))
    } else {
        let word = scope.try_local(constant("Nat")).unwrap();
        let bounded = scope
            .try_local(app(
                "Nat.lt",
                [word.term().clone(), constant("ir_byte_limit_v1")],
            ))
            .unwrap();
        let result = (
            word.term().clone(),
            bound(word.term().clone(), bounded.term().clone()),
        );
        parameters.extend([word, bounded]);
        result
    };
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let canonical = canonical_pointer(&mut a, model.context().clone(), word.clone(), &bounded);
    let actual_operand = if change == Change::NullCarrier {
        app("IRScalar.ptr_", [nat(0)])
    } else {
        canonical.value.clone()
    };
    let before = f.current(actual_operand.clone(), pointer(9));
    let mut operand = actual_operand;
    let mut input_fit = canonical.fits;
    let mut recovery = canonical.address;
    let mut bounded = bounded;
    match change {
        Change::Operand => {
            let other =
                canonical_pointer(&mut a, model.context().clone(), nat(23), &literal_bound(23));
            operand = other.value;
            input_fit = other.fits;
            recovery = other.address;
        }
        Change::InputFit => input_fit.term = refl(&constant("Bool"), constant("Bool.false")),
        Change::Recovery => {
            recovery.term = refl(&app("IROption", [constant("Nat")]), some("Nat", nat(24)))
        }
        Change::Address => {
            // Every endpoint agrees with the proposed address and its genuine
            // bound, but the original proof still recovers sixteen.
            recovery.right = some("Nat", nat(17));
        }
        Change::Bound => {
            bounded = bound(word.clone(), refl(&constant("Bool"), constant("Bool.true")))
        }
        Change::NullCarrier => {
            input_fit = PendingEquality::candidate(
                constant("Bool"),
                app(
                    "ir_byte_value_matches_v1",
                    [
                        model.context().clone(),
                        constant("IRTy.ptr_"),
                        operand.clone(),
                    ],
                ),
                constant("Bool.true"),
                refl(&constant("Bool"), constant("Bool.true")),
            );
            recovery = PendingEquality::candidate(
                app("IROption", [constant("Nat")]),
                app("ir_byte_pointer_address_v1", [operand.clone()]),
                some("Nat", word.clone()),
                refl(
                    &app("IROption", [constant("Nat")]),
                    some("Nat", word.clone()),
                ),
            );
        }
        _ => {}
    }
    // Wrong reached SSA still gets a fully genuine candidate for its own
    // proposed word. The fetched scalar transfer must catch the discrepancy.
    let proposed_word = match change {
        Change::Operand => nat(23),
        Change::Address => nat(17),
        _ => word.clone(),
    };
    let proposed_bound = match change {
        Change::Operand => literal_bound(23),
        Change::Address => literal_bound(17),
        _ => bounded,
    };
    let operations = a.operations();
    let locals = a.local_scope().allocated();
    let shared = a
        .byte_ptr_to_int(
            model.context().clone(),
            &destination,
            operand,
            proposed_word,
            input_fit,
            recovery,
            proposed_bound,
        )
        .unwrap();
    assert_eq!(a.operations() - operations, 2);
    assert_eq!(a.local_scope().allocated(), locals);
    if change == Change::None && numeral == Some(16) {
        for field in [1, 3] {
            let mut fields = shared
                .evaluated
                .left()
                .get_app_args()
                .iter()
                .map(|field| (**field).clone())
                .collect::<Vec<_>>();
            fields[field] = if field == 1 {
                constant("IRCastOp.inttoptr")
            } else {
                app("IRTy.uint_", [nat(32)])
            };
            let claim = eq(
                &constant("IRStepResult"),
                app("ir_byte_cast_eval_v1", fields),
                shared.evaluated.right().clone(),
            );
            replay(
                &a.local_scope().close(&claim).unwrap(),
                &a.local_scope().close(shared.evaluated.term()).unwrap(),
                false,
            );
        }
    }
    let checks = site
        .scalar_checks(&model, &before, shared.value.clone())
        .unwrap();
    let evaluated = a
        .convert_endpoints(
            shared.evaluated,
            checks.evaluation,
            app("IRStepResult.value", [shared.value.clone()]),
        )
        .unwrap();
    let operands = a
        .conversion(constant("Bool"), checks.operands, constant("Bool.true"))
        .unwrap();
    let result = a
        .congruence(shared.fits, constant("Bool"), |fits| {
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
    if change == Change::None && numeral == Some(16) {
        for field in 0..5 {
            let mut wrong = site.clone();
            let mut fields = site
                .instruction
                .get_app_args()
                .iter()
                .map(|field| (**field).clone())
                .collect::<Vec<_>>();
            match field {
                0 => fields[0] = constant("IRCastOp.inttoptr"),
                1 => fields[1] = constant("IRTy.bool_"),
                2 => fields[2] = app("IRTy.uint_", [nat(32)]),
                3 => fields[3] = nat(u64::from(f.alternate.index())),
                _ => wrong.results = list("Nat", &[nat(u64::from(f.result.index()) + 1)]),
            }
            wrong.instruction = app("IRInst.cast", fields);
            assert!(
                wrong
                    .scalar_value(
                        &mut a,
                        &model,
                        &before,
                        shared.value.clone(),
                        premises.clone()
                    )
                    .is_err()
            );
        }
        let other = fixture(CastOp::PtrToInt, Ty::Ptr, Ty::U64);
        let other_reflected =
            reflect_core_module_v1(&other.module, &[(other.function, 4096)]).unwrap();
        let other_model = MachineModel::new(constant("Nat"), &other_reflected, providers());
        assert!(
            site.scalar_checks(&other_model, &before, shared.value.clone())
                .is_err()
        );
    }
    let transfer = site
        .scalar_value(&mut a, &model, &before, shared.value, premises)
        .unwrap();
    assert_eq!(transfer.current().world, before.world);
    let expected_word = if change == Change::Output {
        nat(24)
    } else {
        word
    };
    let mut expected = f.expected(
        &before,
        app("IRScalar.int_", [expected_word]),
        if change == Change::Pc { 3 } else { 2 },
        1,
    );
    if change == Change::World {
        expected.world = world(174, 37, 9);
    }
    let claim = eq(
        &model.config_type(),
        model.run(
            &NatTerm::literal(if change == Change::Fuel { 2 } else { 1 }),
            before.running(&model),
        ),
        expected.running(&model),
    );
    let proof = transfer.run().equality().term().clone();
    drop(a);
    (
        close(&scope, &parameters, claim, true),
        close(&scope, &parameters, proof, false),
    )
}

#[test]
fn ptr_to_int_authored_fetched_cast_preserves_symbolic_boundary_bits_and_whole_world() {
    for destination in [Ty::I64, Ty::U64] {
        for word in [Some(0), Some(1), Some(1 << 63), Some(u64::MAX), None] {
            let (claim, proof) = fetched(destination.clone(), word, Change::None);
            replay(&claim, &proof, true);
        }
    }
}

#[test]
fn ptr_to_int_authored_fetched_cast_refuses_forged_evidence_ssa_output_pc_fuel_world() {
    for change in [
        Change::Operand,
        Change::InputFit,
        Change::Recovery,
        Change::Address,
        Change::Bound,
        Change::NullCarrier,
        Change::Output,
        Change::Pc,
        Change::Fuel,
        Change::World,
    ] {
        let (claim, proof) = fetched(
            Ty::I64,
            Some(if change == Change::NullCarrier { 0 } else { 16 }),
            change,
        );
        replay(&claim, &proof, false);
    }
}

#[test]
fn ptr_to_int_closed_factory_preserves_caller_free_and_outer_bound_contexts() {
    let mut scope = Scope::new();
    let context = scope.try_local(constant("IRByteContextV1")).unwrap();
    let operand = scope.try_local(constant("IRScalar")).unwrap();
    let word = scope.try_local(constant("Nat")).unwrap();
    let input = scope
        .try_local(eq(
            &constant("Bool"),
            app(
                "ir_byte_value_matches_v1",
                [
                    context.term().clone(),
                    constant("IRTy.ptr_"),
                    operand.term().clone(),
                ],
            ),
            constant("Bool.true"),
        ))
        .unwrap();
    let recovery = scope
        .try_local(eq(
            &app("IROption", [constant("Nat")]),
            app("ir_byte_pointer_address_v1", [operand.term().clone()]),
            some("Nat", word.term().clone()),
        ))
        .unwrap();
    let bounded = scope
        .try_local(app(
            "Nat.lt",
            [word.term().clone(), constant("ir_byte_limit_v1")],
        ))
        .unwrap();
    let parameters = [context, operand, word, input, recovery, bounded];
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    for outer_bound in [false, true] {
        let args = if outer_bound {
            [
                Expr::bvar(5),
                Expr::bvar(4),
                Expr::bvar(3),
                Expr::bvar(2),
                Expr::bvar(1),
                Expr::bvar(0),
            ]
        } else {
            parameters.each_ref().map(|p| p.term().clone())
        };
        let input = PendingEquality::candidate(
            constant("Bool"),
            app(
                "ir_byte_value_matches_v1",
                [args[0].clone(), constant("IRTy.ptr_"), args[1].clone()],
            ),
            constant("Bool.true"),
            args[3].clone(),
        );
        let recovery = PendingEquality::candidate(
            app("IROption", [constant("Nat")]),
            app("ir_byte_pointer_address_v1", [args[1].clone()]),
            some("Nat", args[2].clone()),
            args[4].clone(),
        );
        let candidate = a
            .byte_ptr_to_int(
                args[0].clone(),
                &Ty::U64,
                args[1].clone(),
                args[2].clone(),
                input,
                recovery,
                bound(args[2].clone(), args[5].clone()),
            )
            .unwrap();
        for equality in [candidate.fits, candidate.evaluated] {
            let (claim, proof) = if outer_bound {
                let mut claim = equality.proposition();
                let mut template = equality.term().clone();
                let types = [
                    constant("IRByteContextV1"),
                    constant("IRScalar"),
                    constant("Nat"),
                    eq(
                        &constant("Bool"),
                        app(
                            "ir_byte_value_matches_v1",
                            [Expr::bvar(2), constant("IRTy.ptr_"), Expr::bvar(1)],
                        ),
                        constant("Bool.true"),
                    ),
                    eq(
                        &app("IROption", [constant("Nat")]),
                        app("ir_byte_pointer_address_v1", [Expr::bvar(2)]),
                        some("Nat", Expr::bvar(1)),
                    ),
                    app("Nat.lt", [Expr::bvar(2), constant("ir_byte_limit_v1")]),
                ];
                for ty in types.into_iter().rev() {
                    claim = Expr::pi(BinderInfo::Default, ty.clone(), claim);
                    template = Expr::lam(BinderInfo::Default, ty, template);
                }
                (claim, template)
            } else {
                (
                    parameters
                        .iter()
                        .rev()
                        .fold(equality.proposition(), |body, p| p.pi(body)),
                    parameters
                        .iter()
                        .rev()
                        .fold(equality.term().clone(), |body, p| p.lam(body)),
                )
            };
            replay(
                &a.local_scope().close(&claim).unwrap(),
                &a.local_scope().close(&proof).unwrap(),
                true,
            );
        }
    }
}

#[test]
fn ptr_to_int_factory_rejects_context_word_types_and_retains_charged_refusals() {
    let f = fixture(CastOp::PtrToInt, Ty::Ptr, Ty::I64);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let context = model.context().clone();
    let other = fixture(CastOp::PtrToInt, Ty::Ptr, Ty::U64);
    let other_reflected = reflect_core_module_v1(&other.module, &[(other.function, 4096)]).unwrap();
    let other_model = MachineModel::new(constant("Nat"), &other_reflected, providers());
    let input = pointer(16);
    let fit = PendingEquality::candidate(
        constant("Bool"),
        app(
            "ir_byte_value_matches_v1",
            [context.clone(), constant("IRTy.ptr_"), input.clone()],
        ),
        constant("Bool.true"),
        refl(&constant("Bool"), constant("Bool.true")),
    );
    let recovery = PendingEquality::candidate(
        app("IROption", [constant("Nat")]),
        app("ir_byte_pointer_address_v1", [input.clone()]),
        some("Nat", nat(16)),
        refl(&app("IROption", [constant("Nat")]), some("Nat", nat(16))),
    );
    for remaining in 0..2 {
        let mut scope = Scope::new();
        let mut policy = limits();
        policy.max_operations = remaining + 1;
        let mut a = Assembler::new(&mut scope, policy).unwrap();
        a.compose(
            PendingEquality::reflexive(constant("Bool"), constant("Bool.true")),
            PendingEquality::reflexive(constant("Bool"), constant("Bool.true")),
        )
        .unwrap();
        assert!(
            a.byte_ptr_to_int(
                context.clone(),
                &Ty::I64,
                input.clone(),
                nat(16),
                fit.clone(),
                recovery.clone(),
                literal_bound(16)
            )
            .is_err()
        );
        assert_eq!(a.operations(), remaining + 1);
        assert_eq!(a.local_scope().allocated(), 0);
    }
    for case in 0..4 {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let result = a.byte_ptr_to_int(
            if case == 0 {
                other_model.context().clone()
            } else {
                context.clone()
            },
            if case == 1 { &Ty::U32 } else { &Ty::I64 },
            input.clone(),
            if case == 2 { nat(17) } else { nat(16) },
            fit.clone(),
            recovery.clone(),
            literal_bound(if case == 3 { 17 } else { 16 }),
        );
        assert!(result.is_err());
        assert_eq!(a.operations(), 1);
        assert_eq!(a.local_scope().allocated(), 0);
    }
    let (claim, proof) = fetched(Ty::I64, Some(16), Change::None);
    replay(&claim, &proof, true);
}
