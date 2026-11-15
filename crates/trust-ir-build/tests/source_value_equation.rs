// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "clean-tv-anchor")]

use trust_ir::inst::{BinOp, Inst};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, FuncTyId, Function, InstrNode, Module, Ty, ValueId,
};
use trust_ir_build::clean_kernel::env::TrustedEnvExt;
use trust_ir_build::clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, FVarId, Level, MmAxiomOnlyGuard, Name,
    set_mm_axiom_only,
};
use trust_ir_build::{SourceValueEquationError, check_uint_source_value_equation};

fn uint(width: u32) -> Expr {
    Expr::const_str(&format!("UInt{width}"))
}
fn to_nat(width: u32, x: Expr) -> Expr {
    Expr::app(Expr::const_str(&format!("UInt{width}.toNat")), x)
}
fn ty(width: u32) -> Ty {
    match width {
        8 => Ty::U8,
        16 => Ty::U16,
        32 => Ty::U32,
        64 => Ty::U64,
        _ => panic!("fixture width"),
    }
}
fn modulus(width: u32) -> Expr {
    Expr::nat_lit_u128(1u128 << width)
}
fn eq(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("Nat"), lhs, rhs],
    )
}
fn refl(e: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Nat"), e],
    )
}
fn lams(width: u32, arity: u32, mut e: Expr) -> Expr {
    for _ in 0..arity {
        e = Expr::lam(BinderInfo::Default, uint(width), e);
    }
    e
}
fn pis(width: u32, arity: u32, mut e: Expr) -> Expr {
    for _ in 0..arity {
        e = Expr::pi(BinderInfo::Default, uint(width), e);
    }
    e
}
fn source_type(width: u32, arity: u32) -> Expr {
    let mut t = uint(width);
    for _ in 0..arity {
        t = Expr::arrow(uint(width), t);
    }
    t
}

fn add_source(env: &mut Environment, name: Name, width: u32, arity: u32, value: Expr) -> Name {
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: source_type(width, arity),
        value: lams(width, arity, value),
        is_reducible: true,
    })
    .unwrap();
    name
}
fn proposal(source: &Name, width: u32, arity: u32, rhs: Expr) -> Declaration {
    let lhs = to_nat(
        width,
        Expr::apps(
            Expr::const_(source.clone(), vec![]),
            (0..arity).map(|i| Expr::bvar(arity - 1 - i)),
        ),
    );
    Declaration::Theorem {
        name: Name::from_string("Producer.claim"),
        level_params: vec![],
        type_: pis(width, arity, eq(lhs.clone(), rhs)),
        value: lams(width, arity, refl(lhs)),
    }
}
fn binary_module(width: u32, op: BinOp) -> Module {
    let t = ty(width);
    let mut m = Module::new("source-value");
    m.func_types.push(FuncTy {
        params: vec![t.clone(), t.clone()],
        returns: vec![t.clone()],
        is_vararg: false,
        abi: None,
    });
    let mut f = Function::new(
        FuncId::new(0),
        "selected",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    b.params = vec![(ValueId::new(0), t.clone()), (ValueId::new(1), t.clone())];
    b.body.push(
        InstrNode::new(Inst::BinOp {
            op,
            ty: t,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    f.blocks.push(b);
    m.try_add_function(f).unwrap();
    m
}
fn const_module(value: i128) -> Module {
    let mut m = Module::new("source-value-constant");
    m.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut f = Function::new(
        FuncId::new(0),
        "selected",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    b.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(value),
        })
        .with_result(ValueId::new(0)),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    f.blocks.push(b);
    m.try_add_function(f).unwrap();
    m
}
fn uint_const(value: u64) -> Expr {
    Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(value))
}
fn constant_pair() -> (Module, Environment, Name, Declaration) {
    let m = const_module(1);
    let mut e = Environment::with_prelude();
    let s = add_source(
        &mut e,
        Name::from_string("Original.constant"),
        32,
        0,
        uint_const(1),
    );
    let p = proposal(&s, 32, 0, Expr::nat_lit(1u64));
    (m, e, s, p)
}

#[test]
fn source_value_equation_independently_checks_actual_modules_and_sources_at_all_widths() {
    for width in [8, 16, 32, 64] {
        for (operation, op) in [("add", BinOp::Add), ("mul", BinOp::Mul)] {
            let mut env = Environment::with_prelude();
            let source = add_source(
                &mut env,
                Name::from_string("Original")
                    .str(operation)
                    .num(u64::from(width)),
                width,
                2,
                Expr::apps(
                    Expr::const_str(&format!("UInt{width}.{operation}")),
                    [Expr::bvar(1), Expr::bvar(0)],
                ),
            );
            let m = binary_module(width, op);
            let before = m.clone();
            let rhs = Expr::apps(
                Expr::const_str("Nat.mod"),
                [
                    Expr::apps(
                        Expr::const_str(&format!("Nat.{operation}")),
                        [to_nat(width, Expr::bvar(1)), to_nat(width, Expr::bvar(0))],
                    ),
                    modulus(width),
                ],
            );
            let proposed = proposal(&source, width, 2, rhs);
            let checked =
                check_uint_source_value_equation(&m, FuncId::new(0), &env, &source, &proposed)
                    .unwrap();
            assert!(core::ptr::eq(checked.module(), &m));
            assert!(core::ptr::eq(checked.function(), &m.functions[0]));
            assert!(core::ptr::eq(checked.environment(), &env));
            assert_eq!(checked.source(), &source);
            assert_eq!(
                checked.source_closure_digest(),
                &env.closure_digest(&source).unwrap()
            );
            let Declaration::Theorem { type_, value, .. } = &proposed else {
                unreachable!()
            };
            assert_eq!(checked.judgment(), type_);
            assert_eq!(checked.proof(), value);
            assert_eq!(
                m, before,
                "checking a value equation cannot install evidence or a license"
            );
        }
    }
}

#[test]
fn source_value_equation_rejects_wrong_operator_literal_goal_and_open_proof() {
    let (module, env, source, proposed) = constant_pair();
    let mut wrong = module.clone();
    let Inst::Const { value, .. } = &mut wrong.functions[0].blocks[0].body[0].inst else {
        unreachable!()
    };
    *value = Constant::Int(2);
    assert!(
        check_uint_source_value_equation(&wrong, FuncId::new(0), &env, &source, &proposed).is_err()
    );
    let Declaration::Theorem { name, type_, .. } = &proposed else {
        unreachable!()
    };
    for (claimed_goal, proof) in [
        (
            eq(Expr::nat_lit(0u64), Expr::nat_lit(0u64)),
            refl(Expr::nat_lit(0u64)),
        ),
        (type_.clone(), Expr::fvar(FVarId::new(0))),
        (type_.clone(), Expr::bvar(0)),
        (type_.clone(), Expr::const_str("Unknown.proof")),
    ] {
        let forged = Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: claimed_goal,
            value: proof,
        };
        assert!(
            check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &forged)
                .is_err()
        );
    }
    let mut env = Environment::with_prelude();
    let source = add_source(
        &mut env,
        Name::from_string("Original.add"),
        32,
        2,
        Expr::apps(
            Expr::const_str("UInt32.add"),
            [Expr::bvar(1), Expr::bvar(0)],
        ),
    );
    let proposed = proposal(
        &source,
        32,
        2,
        Expr::apps(
            Expr::const_str("Nat.mod"),
            [
                Expr::apps(
                    Expr::const_str("Nat.add"),
                    [to_nat(32, Expr::bvar(1)), to_nat(32, Expr::bvar(0))],
                ),
                modulus(32),
            ],
        ),
    );
    assert!(
        check_uint_source_value_equation(
            &binary_module(32, BinOp::Mul),
            FuncId::new(0),
            &env,
            &source,
            &proposed
        )
        .is_err()
    );
}

#[test]
fn source_value_equation_preserves_input_order_and_external_source_mapping() {
    let mut env = Environment::with_prelude();
    let source = add_source(
        &mut env,
        Name::from_string("Original.first"),
        32,
        2,
        Expr::bvar(1),
    );
    let mut module = binary_module(32, BinOp::Add);
    module.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    })];
    let proposed = proposal(&source, 32, 2, to_nat(32, Expr::bvar(1)));
    check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &proposed).unwrap();
    let mut wrong = module.clone();
    wrong.functions[0].blocks[0].body[0].inst = Inst::Return {
        values: vec![ValueId::new(1)],
    };
    assert!(
        check_uint_source_value_equation(&wrong, FuncId::new(0), &env, &source, &proposed).is_err()
    );
    let alternate = add_source(
        &mut env,
        Name::from_string("Original.alternate"),
        32,
        2,
        Expr::bvar(1),
    );
    assert!(
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &alternate, &proposed)
            .is_err(),
        "even a same-valued alternate source cannot be witness-selected"
    );
    assert!(env.forget_decl(&source));
    add_source(&mut env, source.clone(), 32, 2, Expr::bvar(0));
    assert!(
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &proposed)
            .is_err(),
        "same-name changed source keeps the claimed goal but changes its actual meaning"
    );
    let missing = Name::from_string("Original.missing");
    assert!(
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &missing, &proposed)
            .is_err()
    );
    let typed = Name::from_string("Original").num(0);
    let printed = Name::from_string("Original").str("0");
    assert_ne!(typed, printed);
    add_source(&mut env, printed.clone(), 32, 0, uint_const(1));
    let constant = const_module(1);
    let printed_proof = proposal(&printed, 32, 0, Expr::nat_lit(1u64));
    check_uint_source_value_equation(&constant, FuncId::new(0), &env, &printed, &printed_proof)
        .unwrap();
    assert!(
        check_uint_source_value_equation(&constant, FuncId::new(0), &env, &typed, &printed_proof)
            .is_err()
    );
}

#[test]
fn source_value_equation_checks_complete_module_and_actual_signature() {
    let (module, env, source, proposed) = constant_pair();
    for mutation in [0, 1, 2] {
        let mut wrong = module.clone();
        match mutation {
            0 => {
                let mut f = wrong.functions[0].clone();
                f.id = FuncId::new(2);
                f.name = "unrelated".into();
                f.ty = FuncTyId::new(999);
                wrong.functions.push(f);
            }
            1 => {
                let f = wrong.functions[0].clone();
                wrong.functions.push(f);
            }
            2 => {
                let mut f = wrong.functions[0].clone();
                f.id = FuncId::new(2);
                f.name = "unrelated".into();
                f.blocks[0].body[1].inst = Inst::Return {
                    values: vec![ValueId::new(999)],
                };
                wrong.functions.push(f);
            }
            _ => unreachable!(),
        }
        assert!(
            matches!(
                check_uint_source_value_equation(&wrong, FuncId::new(0), &env, &source, &proposed),
                Err(SourceValueEquationError::InvalidModule(_))
            ),
            "an unrelated invalid body/ID must not be filtered out"
        );
    }
    assert!(
        check_uint_source_value_equation(&module, FuncId::new(999), &env, &source, &proposed)
            .is_err()
    );
    let mut wrong = module.clone();
    wrong.func_types[0].returns = vec![Ty::I32];
    let Inst::Const { ty, .. } = &mut wrong.functions[0].blocks[0].body[0].inst else {
        unreachable!()
    };
    *ty = Ty::I32;
    assert!(
        check_uint_source_value_equation(&wrong, FuncId::new(0), &env, &source, &proposed).is_err()
    );
    let mut wrong = module.clone();
    wrong.func_types[0].returns = vec![Ty::U64];
    let Inst::Const { ty, .. } = &mut wrong.functions[0].blocks[0].body[0].inst else {
        unreachable!()
    };
    *ty = Ty::U64;
    assert!(
        check_uint_source_value_equation(&wrong, FuncId::new(0), &env, &source, &proposed).is_err()
    );
}

#[test]
fn source_value_equation_refuses_structural_counterfeit_and_separate_axiom_closures() {
    let (module, mut env, source, proposed) = constant_pair();
    let Declaration::Theorem { type_, .. } = &proposed else {
        unreachable!()
    };
    let axiom = Name::from_string("Domain.assumption");
    env.add_decl(Declaration::Axiom {
        name: axiom.clone(),
        level_params: vec![],
        type_: type_.clone(),
    })
    .unwrap();
    let untrusted = Declaration::Theorem {
        name: Name::from_string("Producer.axiomProof"),
        level_params: vec![],
        type_: type_.clone(),
        value: Expr::const_(axiom, vec![]),
    };
    assert!(
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &untrusted)
            .is_err()
    );
    assert!(env.forget_decl(&source));
    // SOUNDNESS: deliberately non-certifying test input; the consumer must
    // refuse the source's StructuralOnly provenance despite its valid value.
    env.add_decl_structural(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: uint(32),
        value: uint_const(1),
        is_reducible: true,
    })
    .unwrap();
    assert!(
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &proposed)
            .is_err()
    );
    assert!(env.forget_decl(&source));
    // SOUNDNESS: deliberately unchecked test source; its status cannot stand
    // in for original-definition checking at the public consumer seam.
    env.add_decl_unchecked(Declaration::Definition {
        name: source.clone(),
        level_params: vec![],
        type_: uint(32),
        value: uint_const(1),
        is_reducible: true,
    });
    assert!(
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &proposed)
            .is_err()
    );
    let mut env = Environment::with_prelude();
    let foundation = Name::from_string("propext");
    assert!(env.forget_decl(&foundation));
    env.add_decl(Declaration::Axiom {
        name: foundation.clone(),
        level_params: vec![],
        type_: uint(32),
    })
    .unwrap();
    let source = add_source(
        &mut env,
        source,
        32,
        0,
        Expr::let_named(
            Name::from_string("unused"),
            uint(32),
            Expr::const_(foundation, vec![]),
            uint_const(1),
            false,
        ),
    );
    let proposed = proposal(&source, 32, 0, Expr::nat_lit(1u64));
    let refusal =
        match check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &proposed) {
            Err(error) => error.to_string(),
            Ok(_) => panic!("accepted the counterfeit foundational axiom dependency"),
        };
    assert!(refusal.contains("NonCanonicalFoundation"), "{refusal}");
}

#[test]
fn source_value_equation_does_not_treat_mm_import_success_as_kernel_admission() {
    let (module, env, source, proposed) = constant_pair();
    let _guard = MmAxiomOnlyGuard::enter();
    set_mm_axiom_only(true);
    assert!(
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &proposed)
            .is_err()
    );
}

#[test]
fn source_value_equation_refuses_calls_mixed_widths_and_witness_arity() {
    let mut env = Environment::with_prelude();
    let source = add_source(
        &mut env,
        Name::from_string("Original.first"),
        32,
        2,
        Expr::bvar(1),
    );
    let proof = proposal(&source, 32, 2, to_nat(32, Expr::bvar(1)));
    let mut mixed = binary_module(32, BinOp::Add);
    mixed.func_types[0].params[0] = Ty::U64;
    mixed.functions[0].blocks[0].params[0].1 = Ty::U64;
    mixed.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    })];
    assert!(trust_ir_build::validate_module(&mixed).is_empty());
    assert!(matches!(
        check_uint_source_value_equation(&mixed, FuncId::new(0), &env, &source, &proof),
        Err(SourceValueEquationError::Unsupported(_))
    ));
    let mut calls = binary_module(32, BinOp::Add);
    let mut callee = calls.functions[0].clone();
    callee.id = FuncId::new(1);
    callee.name = "callee".into();
    calls.functions.push(callee);
    calls.functions[0].blocks[0].body[0].inst = Inst::Call {
        callee: FuncId::new(1),
        args: vec![ValueId::new(0), ValueId::new(1)],
    };
    assert!(
        trust_ir_build::validate_module(&calls).is_empty(),
        "{:?}",
        trust_ir_build::validate_module(&calls)
    );
    assert!(matches!(
        check_uint_source_value_equation(&calls, FuncId::new(0), &env, &source, &proof),
        Err(SourceValueEquationError::Unsupported(_))
    ));
    let (mut module, env, source, proof) = constant_pair();
    module.func_types[0].params.push(Ty::U32);
    module.functions[0].blocks[0]
        .params
        .push((ValueId::new(1), Ty::U32));
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert!(matches!(
        check_uint_source_value_equation(&module, FuncId::new(0), &env, &source, &proof),
        Err(SourceValueEquationError::Unsupported(_))
    ));
}
