// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Replay complete FNV source-equation DATA using the production consumer.
//! The original checked definitions are separate caller-selected fixture inputs;
//! the proposed theorem supplies neither its own goal nor source identity.

use super::{DefinitionData, Fixture, load};
use trust_ir::{
    FuncTyId,
    inst::{BinOp, Inst},
};
use trust_ir_build::check_uint_source_value_equation;
use trust_ir_build::clean_kernel::{BinderInfo, Declaration, Expr, Name};

macro_rules! fnv_raw {
    ($case:literal, $file:expr) => {
        include_bytes!(concat!(
            "../fixtures/source_value_equations/fnv/",
            $case,
            "/",
            $file
        ))
    };
}
macro_rules! fnv_definition {
    ($case:literal, $index:literal) => {
        DefinitionData {
            name: fnv_raw!($case, concat!("definition-", $index, ".name.bin")),
            type_: fnv_raw!($case, concat!("definition-", $index, ".type.bin")),
            value: fnv_raw!($case, concat!("definition-", $index, ".value.bin")),
            is_reducible: false,
        }
    };
}
macro_rules! fnv_fixture {
    ($case:literal) => {
        Fixture {
            expected_source: $case,
            module: fnv_raw!($case, "module.bin"),
            definitions: vec![fnv_definition!($case, "0"), fnv_definition!($case, "1")],
            theorem_name: fnv_raw!($case, "theorem.name.bin"),
            theorem_type: fnv_raw!($case, "theorem.type.bin"),
            theorem_value: fnv_raw!($case, "theorem.value.bin"),
            original_source_digest: fnv_raw!($case, "source-closure-digest.bin"),
        }
    };
}
fn fixtures() -> [Fixture; 2] {
    [
        fnv_fixture!("trust_cg_fnv128_step_lo"),
        fnv_fixture!("trust_cg_fnv128_step_hi"),
    ]
}

#[test]
fn complete_fnv_source_equations_replay_in_the_independent_ir_consumer() {
    for fixture in fixtures() {
        let (module, environment, source, proposed, function) = load(&fixture);
        assert_eq!(module.functions.len(), 2, "complete actual carrier module");
        assert!(trust_ir_build::validate_module_for_codegen(&module).is_empty());
        let before = module.clone();
        let checked =
            check_uint_source_value_equation(&module, function, &environment, &source, &proposed)
                .unwrap_or_else(|e| panic!("{}: {e}", fixture.expected_source));
        assert!(core::ptr::eq(checked.module(), &module));
        assert_eq!(checked.function().id, function);
        let Declaration::Theorem { type_, value, .. } = &proposed else {
            unreachable!()
        };
        assert_eq!(checked.judgment(), type_);
        assert_eq!(checked.proof(), value);
        assert_eq!(
            module, before,
            "source-value replay changes no body license or grade"
        );
    }
}

#[test]
fn complete_fnv_source_equations_reject_body_and_function_mapping_mutants() {
    for fixture in fixtures() {
        let (module, environment, source, proposed, function) = load(&fixture);
        let mut changed = module.clone();
        let body = changed
            .functions
            .iter_mut()
            .find(|f| f.id == function)
            .unwrap();
        let node = body
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.body)
            .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Xor, .. }))
            .unwrap();
        let Inst::BinOp { op, .. } = &mut node.inst else {
            unreachable!()
        };
        *op = BinOp::Or;
        assert!(
            check_uint_source_value_equation(&changed, function, &environment, &source, &proposed)
                .is_err()
        );
        let other = module
            .functions
            .iter()
            .find(|f| f.id != function)
            .unwrap()
            .id;
        assert!(
            check_uint_source_value_equation(&module, other, &environment, &source, &proposed)
                .is_err()
        );
        let mut malformed = module.clone();
        malformed
            .functions
            .iter_mut()
            .find(|f| f.id != function)
            .unwrap()
            .ty = FuncTyId::new(u32::MAX);
        assert!(
            check_uint_source_value_equation(
                &malformed,
                function,
                &environment,
                &source,
                &proposed
            )
            .is_err(),
            "a malformed unselected body cannot be hidden from whole-module validation"
        );
    }
}

#[test]
fn complete_fnv_source_equations_reject_forged_proofs_and_changed_original_definitions() {
    for fixture in fixtures() {
        let (module, mut environment, source, proposed, function) = load(&fixture);
        let Declaration::Theorem {
            name,
            level_params,
            type_,
            ..
        } = &proposed
        else {
            unreachable!()
        };
        let wrong_proof = Declaration::Theorem {
            name: name.clone(),
            level_params: level_params.clone(),
            type_: type_.clone(),
            value: Expr::const_str("True.intro"),
        };
        assert!(
            check_uint_source_value_equation(
                &module,
                function,
                &environment,
                &source,
                &wrong_proof
            )
            .is_err()
        );
        let wrong_goal = Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::const_str("True"),
            value: Expr::const_str("True.intro"),
        };
        assert!(
            check_uint_source_value_equation(&module, function, &environment, &source, &wrong_goal)
                .is_err(),
            "a true theorem is not a proof of the consumer's reconstructed source equation"
        );
        let type_ = environment.get_const(&source).unwrap().type_.clone();
        assert!(environment.forget_decl(&source));
        let arity = if fixture.expected_source.ends_with("_lo") {
            2
        } else {
            3
        };
        let mut value = Expr::app(Expr::const_str("UInt64.ofNat"), Expr::nat_lit(0));
        for _ in 0..arity {
            value = Expr::lam(BinderInfo::Default, Expr::const_str("UInt64"), value);
        }
        environment
            .add_decl(Declaration::Definition {
                name: Name::from_string(fixture.expected_source),
                level_params: vec![],
                type_,
                value,
                is_reducible: false,
            })
            .expect("changed source still kernel-checks");
        assert!(
            check_uint_source_value_equation(&module, function, &environment, &source, &proposed)
                .is_err(),
            "the same name and type cannot authenticate another original source body"
        );
    }
}
