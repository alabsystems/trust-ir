// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "clean-tv-anchor")]

//! Typed equation transport tests over actual kernel-checked definitions.
//! Source parsing, proof search and source-to-machine refinement are separate.
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, Ty, ValueId,
};
use trust_ir_build::clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, FVarId, Level, Name,
};
use trust_ir_build::{
    SourceValueEquationError, check_scalar_source_value_equation, check_uint_source_value_equation,
};

fn source_type(ty: &Ty) -> Expr {
    Expr::const_str(match ty {
        Ty::Bool => "Bool",
        Ty::U8 => "UInt8",
        Ty::U16 => "UInt16",
        Ty::U32 => "UInt32",
        Ty::U64 => "UInt64",
        _ => panic!("fixture scalar type"),
    })
}

fn image(ty: &Ty, value: Expr) -> Expr {
    match ty {
        Ty::Bool => value,
        Ty::U8 => Expr::app(Expr::const_str("UInt8.toNat"), value),
        Ty::U16 => Expr::app(Expr::const_str("UInt16.toNat"), value),
        Ty::U32 => Expr::app(Expr::const_str("UInt32.toNat"), value),
        Ty::U64 => Expr::app(Expr::const_str("UInt64.toNat"), value),
        _ => panic!("fixture scalar type"),
    }
}

fn bind(parameters: &[Ty], body: Expr, proposition: bool) -> Expr {
    parameters.iter().rev().fold(body, |body, ty| {
        if proposition {
            Expr::pi(BinderInfo::Default, source_type(ty), body)
        } else {
            Expr::lam(BinderInfo::Default, source_type(ty), body)
        }
    })
}

struct Fixture {
    module: Module,
    env: Environment,
    source: Name,
    definition: Declaration,
    theorem: Declaration,
}

fn projection(parameters: &[Ty], projected: usize) -> Fixture {
    let result = &parameters[projected];
    let mut module = Module::new("typed-source-equation");
    module.func_types.push(FuncTy {
        params: parameters.to_vec(),
        returns: vec![result.clone()],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(
        FuncId::new(0),
        "selected",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params = parameters
        .iter()
        .enumerate()
        .map(|(i, ty)| (ValueId::new(i as u32), ty.clone()))
        .collect();
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(projected as u32)],
    }));
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    let arity = parameters.len() as u32;
    let source = Name::from_string("TypedSource.actual");
    let definition = Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: parameters
            .iter()
            .rev()
            .fold(source_type(result), |rest, ty| {
                Expr::arrow(source_type(ty), rest)
            }),
        value: bind(parameters, Expr::bvar(arity - 1 - projected as u32), false),
        is_reducible: true,
    };
    let mut env = Environment::with_prelude();
    env.add_decl(definition.clone()).unwrap();
    let lhs = image(
        result,
        Expr::apps(
            Expr::const_(source.clone(), vec![]),
            (0..arity).map(|i| Expr::bvar(arity - 1 - i)),
        ),
    );
    let rhs = image(result, Expr::bvar(arity - 1 - projected as u32));
    let model = Expr::const_str(if *result == Ty::Bool { "Bool" } else { "Nat" });
    let theorem = Declaration::Theorem {
        name: Name::from_string("Producer.supplied"),
        level_params: vec![],
        type_: bind(
            parameters,
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [model.clone(), lhs.clone(), rhs],
            ),
            true,
        ),
        value: bind(
            parameters,
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [model, lhs],
            ),
            false,
        ),
    };
    Fixture {
        module,
        env,
        source,
        definition,
        theorem,
    }
}

#[test]
fn mixed_parameter_order_and_result_images_replay_at_every_width() {
    for ty in [Ty::U8, Ty::U16, Ty::U32, Ty::U64] {
        let parameters = [Ty::Bool, ty.clone(), Ty::Bool, ty];
        for projected in 0..parameters.len() {
            let f = projection(&parameters, projected);
            check_scalar_source_value_equation(
                &f.module,
                FuncId::new(0),
                &f.env,
                &f.source,
                &f.theorem,
            )
            .unwrap();
            assert!(
                check_uint_source_value_equation(
                    &f.module,
                    FuncId::new(0),
                    &f.env,
                    &f.source,
                    &f.theorem
                )
                .is_err(),
                "the original uniform UInt API must keep refusing mixed signatures"
            );
        }
    }
}

#[test]
fn changed_return_source_and_unused_argument_carrier_cannot_reuse_a_proof() {
    let f = projection(&[Ty::Bool, Ty::U8, Ty::Bool, Ty::U16], 0);
    check_scalar_source_value_equation(&f.module, FuncId::new(0), &f.env, &f.source, &f.theorem)
        .unwrap();
    let mut wrong = f.module.clone();
    let Inst::Return { values } = &mut wrong.functions[0].blocks[0].body[0].inst else {
        panic!("fixture Return")
    };
    values[0] = ValueId::new(2);
    assert!(
        check_scalar_source_value_equation(&wrong, FuncId::new(0), &f.env, &f.source, &f.theorem)
            .is_err()
    );
    assert!(
        check_scalar_source_value_equation(
            &f.module,
            FuncId::new(0),
            &f.env,
            &Name::from_string("Missing.source"),
            &f.theorem
        )
        .is_err()
    );
    let mut wrong = f.module.clone();
    wrong.func_types[0].params[3] = Ty::U32;
    wrong.functions[0].blocks[0].params[3].1 = Ty::U32;
    assert!(
        check_scalar_source_value_equation(&wrong, FuncId::new(0), &f.env, &f.source, &f.theorem)
            .is_err()
    );
}

#[test]
fn unchecked_source_open_proof_and_wrong_closed_proof_are_refused() {
    let f = projection(&[Ty::Bool, Ty::U8], 0);
    let mut unchecked = Environment::with_prelude();
    unchecked.add_decl_structural(f.definition.clone()).unwrap();
    assert!(
        check_scalar_source_value_equation(
            &f.module,
            FuncId::new(0),
            &unchecked,
            &f.source,
            &f.theorem
        )
        .is_err()
    );
    let mut open = f.theorem.clone();
    let Declaration::Theorem { value, .. } = &mut open else {
        panic!("fixture theorem")
    };
    *value = Expr::fvar(FVarId::new(999));
    assert!(
        check_scalar_source_value_equation(&f.module, FuncId::new(0), &f.env, &f.source, &open)
            .is_err()
    );
    let mut wrong = f.theorem.clone();
    let Declaration::Theorem { value, .. } = &mut wrong else {
        panic!("fixture theorem")
    };
    *value = bind(
        &[Ty::Bool, Ty::U8],
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), Expr::const_str("Bool.false")],
        ),
        false,
    );
    assert!(
        check_scalar_source_value_equation(&f.module, FuncId::new(0), &f.env, &f.source, &wrong)
            .is_err()
    );
}

#[test]
fn invalid_unselected_body_still_invalidates_the_complete_module() {
    let mut f = projection(&[Ty::Bool, Ty::U8], 0);
    let mut bad = f.module.functions[0].clone();
    bad.id = FuncId::new(1);
    bad.name = "invalid_nonselected".into();
    let Inst::Return { values } = &mut bad.blocks[0].body[0].inst else {
        panic!("fixture Return")
    };
    values[0] = ValueId::new(u32::MAX);
    f.module.try_add_function(bad).unwrap();
    assert!(matches!(
        check_scalar_source_value_equation(
            &f.module,
            FuncId::new(0),
            &f.env,
            &f.source,
            &f.theorem
        ),
        Err(SourceValueEquationError::InvalidModule(_))
    ));
}

#[test]
fn uniform_uint_keeps_its_original_goal_and_checked_closure() {
    for ty in [Ty::U8, Ty::U16, Ty::U32, Ty::U64] {
        let f = projection(&[ty.clone(), ty], 1);
        let old = check_uint_source_value_equation(
            &f.module,
            FuncId::new(0),
            &f.env,
            &f.source,
            &f.theorem,
        )
        .unwrap();
        let scalar = check_scalar_source_value_equation(
            &f.module,
            FuncId::new(0),
            &f.env,
            &f.source,
            &f.theorem,
        )
        .unwrap();
        assert_eq!(old.judgment(), scalar.judgment());
        assert_eq!(old.source_closure_digest(), scalar.source_closure_digest());
        assert_eq!(
            old.equation_closure_digest(),
            scalar.equation_closure_digest()
        );
    }
}

#[test]
fn boolean_comparison_equations_replay_and_match_the_complete_truth_table() {
    use trust_ir::inst::ICmpOp;
    for op in [ICmpOp::Eq, ICmpOp::Ne] {
        let mut f = projection(&[Ty::Bool, Ty::Bool], 0);
        let block = &mut f.module.functions[0].blocks[0];
        block.body = vec![
            InstrNode::new(Inst::ICmp {
                op,
                ty: Ty::Bool,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ];
        let different = Expr::apps(Expr::const_str("Bool.xor"), [Expr::bvar(1), Expr::bvar(0)]);
        let expression = if op == ICmpOp::Eq {
            Expr::app(Expr::const_str("Bool.not"), different)
        } else {
            different
        };
        let Declaration::Definition { value, .. } = &mut f.definition else {
            panic!("definition")
        };
        *value = bind(&[Ty::Bool, Ty::Bool], expression.clone(), false);
        f.env = Environment::with_prelude();
        f.env.add_decl(f.definition.clone()).unwrap();
        let lhs = Expr::apps(
            Expr::const_(f.source.clone(), vec![]),
            [Expr::bvar(1), Expr::bvar(0)],
        );
        f.theorem = Declaration::Theorem {
            name: Name::from_string("Producer.booleanComparison"),
            level_params: vec![],
            type_: bind(
                &[Ty::Bool, Ty::Bool],
                Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [Expr::const_str("Bool"), lhs.clone(), expression],
                ),
                true,
            ),
            value: bind(
                &[Ty::Bool, Ty::Bool],
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [Expr::const_str("Bool"), lhs],
                ),
                false,
            ),
        };
        check_scalar_source_value_equation(
            &f.module,
            FuncId::new(0),
            &f.env,
            &f.source,
            &f.theorem,
        )
        .unwrap();
        for a in [false, true] {
            for b in [false, true] {
                let output = trust_ir::Interpreter::with_module(&f.module)
                    .execute_func(
                        FuncId::new(0),
                        [
                            trust_ir::InterpretValue::bool(a),
                            trust_ir::InterpretValue::bool(b),
                        ],
                    )
                    .unwrap();
                assert_eq!(output.host_calls, 0);
                assert_eq!(output.returns.len(), 1);
                assert_eq!(
                    output.returns[0].as_bool(),
                    Some(if op == ICmpOp::Eq { a == b } else { a != b })
                );
            }
        }
        let mut changed = f.module.clone();
        let Inst::ICmp { op: predicate, .. } = &mut changed.functions[0].blocks[0].body[0].inst
        else {
            panic!("comparison")
        };
        *predicate = if op == ICmpOp::Eq {
            ICmpOp::Ne
        } else {
            ICmpOp::Eq
        };
        assert!(
            check_scalar_source_value_equation(
                &changed,
                FuncId::new(0),
                &f.env,
                &f.source,
                &f.theorem
            )
            .is_err()
        );
        for predicate in [
            ICmpOp::Ult,
            ICmpOp::Ule,
            ICmpOp::Ugt,
            ICmpOp::Uge,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
        ] {
            let Inst::ICmp { op, .. } = &mut changed.functions[0].blocks[0].body[0].inst else {
                panic!("comparison")
            };
            *op = predicate;
            assert!(
                check_scalar_source_value_equation(
                    &changed,
                    FuncId::new(0),
                    &f.env,
                    &f.source,
                    &f.theorem
                )
                .is_err()
            );
        }
    }
}
