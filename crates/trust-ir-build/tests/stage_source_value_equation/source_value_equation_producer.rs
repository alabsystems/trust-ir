// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "clean-tv-anchor")]

//! DATA-only interoperability with actual Clean-produced modules and terms.
//! The expected original source/environment is fixture input supplied separately
//! from the proposed theorem; no producer goal, digest or status is authority.

use trust_ir::inst::{BinOp, Inst};
use trust_ir::proof::decode_clean_expr_v1;
use trust_ir::{Constant, FuncId, FuncTyId, Module};
use trust_ir_build::clean_kernel::{BinderInfo, Declaration, Environment, Expr, ExprKind, Name};
use trust_ir_build::{SourceValueEquationError, check_uint_source_value_equation};

macro_rules! raw {
    ($case:literal, $file:literal) => {
        include_bytes!(concat!(
            "fixtures/source_value_equations/",
            $case,
            "/",
            $file
        ))
    };
}
macro_rules! definition {
    ($case:literal, $index:literal, $reducible:expr) => {
        DefinitionData {
            name: include_bytes!(concat!(
                "fixtures/source_value_equations/",
                $case,
                "/definition-",
                $index,
                ".name.bin"
            )),
            type_: include_bytes!(concat!(
                "fixtures/source_value_equations/",
                $case,
                "/definition-",
                $index,
                ".type.bin"
            )),
            value: include_bytes!(concat!(
                "fixtures/source_value_equations/",
                $case,
                "/definition-",
                $index,
                ".value.bin"
            )),
            is_reducible: $reducible,
        }
    };
}

struct DefinitionData {
    name: &'static [u8],
    type_: &'static [u8],
    value: &'static [u8],
    is_reducible: bool,
}
struct Fixture {
    expected_source: &'static str,
    module: &'static [u8],
    definitions: Vec<DefinitionData>,
    theorem_name: &'static [u8],
    theorem_type: &'static [u8],
    theorem_value: &'static [u8],
    original_source_digest: &'static [u8],
}

fn fixtures() -> [Fixture; 3] {
    [
        Fixture {
            expected_source: "boundActualEquation",
            module: raw!("boundActualEquation", "module.bin"),
            definitions: vec![definition!("boundActualEquation", "0", false)],
            theorem_name: raw!("boundActualEquation", "theorem.name.bin"),
            theorem_type: raw!("boundActualEquation", "theorem.type.bin"),
            theorem_value: raw!("boundActualEquation", "theorem.value.bin"),
            original_source_digest: raw!("boundActualEquation", "source-closure-digest.bin"),
        },
        Fixture {
            expected_source: "boundField",
            module: raw!("boundField", "module.bin"),
            definitions: vec![
                definition!("boundField", "0", true),
                definition!("boundField", "1", true),
            ],
            theorem_name: raw!("boundField", "theorem.name.bin"),
            theorem_type: raw!("boundField", "theorem.type.bin"),
            theorem_value: raw!("boundField", "theorem.value.bin"),
            original_source_digest: raw!("boundField", "source-closure-digest.bin"),
        },
        Fixture {
            expected_source: "boundMask",
            module: raw!("boundMask", "module.bin"),
            definitions: vec![definition!("boundMask", "0", false)],
            theorem_name: raw!("boundMask", "theorem.name.bin"),
            theorem_type: raw!("boundMask", "theorem.type.bin"),
            theorem_value: raw!("boundMask", "theorem.value.bin"),
            original_source_digest: raw!("boundMask", "source-closure-digest.bin"),
        },
    ]
}

fn expression(bytes: &[u8]) -> Expr {
    decode_clean_expr_v1(bytes).expect("bounded canonical Expr carrier")
}
fn name(bytes: &[u8]) -> Name {
    let e = expression(bytes);
    let ExprKind::Const(name, levels) = e.kind() else {
        panic!("fixture name is not a typed kernel Const")
    };
    assert!(levels.is_empty());
    name.clone()
}
fn load(f: &Fixture) -> (Module, Environment, Name, Declaration, FuncId) {
    let module = trust_ir::binary::deserialize_module(f.module)
        .expect("the complete actual producer module decodes");
    let mut original_environment = Environment::with_prelude();
    for d in &f.definitions {
        original_environment
            .add_decl(Declaration::Definition {
                name: name(d.name),
                level_params: vec![],
                type_: expression(d.type_),
                value: expression(d.value),
                is_reducible: d.is_reducible,
            })
            .expect("independently kernel-check actual original definition data");
    }
    // These expected names are hardcoded caller-side mappings, not read from
    // the proposed theorem. The source declarations are separate env inputs.
    let source = Name::from_string(f.expected_source);
    let function = module
        .functions
        .iter()
        .find(|function| function.name == f.expected_source)
        .expect("the externally selected actual function")
        .id;
    assert_eq!(
        original_environment
            .closure_digest(&source)
            .unwrap()
            .as_slice(),
        f.original_source_digest,
        "the reconstructed actual custom source closure must match the retained original data"
    );
    let proposed = Declaration::Theorem {
        name: name(f.theorem_name),
        level_params: vec![],
        type_: expression(f.theorem_type),
        value: expression(f.theorem_value),
    };
    (module, original_environment, source, proposed, function)
}

#[test]
fn source_value_equation_rechecks_actual_clean_producer_modules_and_full_cic_proofs() {
    for fixture in fixtures() {
        let (module, environment, source, proposed, function) = load(&fixture);
        let before = module.clone();
        let checked =
            check_uint_source_value_equation(&module, function, &environment, &source, &proposed)
                .unwrap_or_else(|error| panic!("{}: {error}", fixture.expected_source));
        assert!(core::ptr::eq(checked.module(), &module));
        assert_eq!(checked.function().id, function);
        let Declaration::Theorem { type_, value, .. } = &proposed else {
            unreachable!()
        };
        assert_eq!(checked.judgment(), type_);
        assert_eq!(checked.proof(), value);
        assert_eq!(
            module, before,
            "an accepted value equation cannot mutate body licenses or grades"
        );
        let bodies: Vec<_> = module
            .functions
            .iter()
            .filter(|f| !f.is_declaration())
            .collect();
        assert_eq!(
            bodies.len(),
            2,
            "retain the actual source and generated boxed entry"
        );
        let helper = bodies.iter().find(|f| f.id != function).unwrap();
        assert_eq!(
            helper.name,
            format!("l_{}___boxed", fixture.expected_source)
        );
        let strict = trust_ir_build::validate_module_for_codegen(&module);
        assert!(
            strict.iter().any(|error| matches!(error,
            trust_ir_build::ValidationError::UngatedBodyForCodegen { function, .. }
                if *function == helper.id.index())),
            "{} helper gate {:?}, strict refusals: {strict:?}",
            fixture.expected_source,
            helper.body_gate
        );
    }
}

#[test]
fn source_value_equation_actual_producer_tamper_controls_rederive_the_selected_ir() {
    let mut literal_controls = 0;
    for fixture in fixtures() {
        let (module, environment, source, proposed, function) = load(&fixture);
        for label in ["operator", "parameter order", "unrelated body"] {
            let mut changed = module.clone();
            match label {
                "operator" => {
                    let selected = changed
                        .functions
                        .iter_mut()
                        .find(|f| f.id == function)
                        .unwrap();
                    let node = selected
                        .blocks
                        .iter_mut()
                        .flat_map(|b| &mut b.body)
                        .find(|n| matches!(n.inst, Inst::BinOp { .. }))
                        .unwrap();
                    let Inst::BinOp { op, .. } = &mut node.inst else {
                        unreachable!()
                    };
                    *op = if *op == BinOp::Add {
                        BinOp::Sub
                    } else {
                        BinOp::Add
                    };
                }
                "parameter order" => {
                    let selected = changed
                        .functions
                        .iter_mut()
                        .find(|f| f.id == function)
                        .unwrap();
                    let entry = selected
                        .blocks
                        .iter_mut()
                        .find(|b| b.id == selected.entry)
                        .unwrap();
                    entry.params.swap(0, 1);
                }
                "unrelated body" => {
                    let helper = changed
                        .functions
                        .iter_mut()
                        .find(|f| !f.is_declaration() && f.id != function)
                        .unwrap();
                    helper.ty = FuncTyId::new(u32::MAX);
                }
                _ => unreachable!(),
            }
            // Mask is symmetric; its parameter swap is the SAME expression up
            // to commutation but this proof procedure may refuse that different
            // exact claimed goal. BoundField/Sub and ActualEquation exercise
            // genuinely noncommutative parameter correspondence as well.
            let result = check_uint_source_value_equation(
                &changed,
                function,
                &environment,
                &source,
                &proposed,
            );
            assert!(
                result.is_err(),
                "{} {label} must re-earn the independently derived goal",
                fixture.expected_source
            );
            if label == "unrelated body" {
                assert!(matches!(
                    result,
                    Err(SourceValueEquationError::InvalidModule(_))
                ));
            }
        }
        let mut changed = module.clone();
        let selected = changed
            .functions
            .iter_mut()
            .find(|f| f.id == function)
            .unwrap();
        if let Some(node) = selected
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.body)
            .find(|n| {
                matches!(
                    n.inst,
                    Inst::Const {
                        value: Constant::Int(_),
                        ..
                    }
                )
            })
        {
            let Inst::Const {
                value: Constant::Int(k),
                ..
            } = &mut node.inst
            else {
                unreachable!()
            };
            *k += 1;
            literal_controls += 1;
            assert!(
                check_uint_source_value_equation(
                    &changed,
                    function,
                    &environment,
                    &source,
                    &proposed
                )
                .is_err()
            );
        }
    }
    assert_eq!(
        literal_controls, 2,
        "both actual literal-bearing source modules were mutated"
    );
}

#[test]
fn source_value_equation_actual_proofs_bind_the_original_definition_and_reject_forged_goals() {
    for fixture in fixtures() {
        let (module, mut environment, source, proposed, function) = load(&fixture);
        let Declaration::Theorem {
            name,
            level_params,
            value,
            ..
        } = &proposed
        else {
            unreachable!()
        };
        let forged = Declaration::Theorem {
            name: name.clone(),
            level_params: level_params.clone(),
            type_: Expr::prop(),
            value: value.clone(),
        };
        assert!(
            check_uint_source_value_equation(&module, function, &environment, &source, &forged)
                .is_err()
        );
        let old = environment.get_const(&source).unwrap();
        let type_ = old.type_.clone();
        assert!(environment.forget_decl(&source));
        let u = Expr::const_str("UInt32");
        environment
            .add_decl(Declaration::Definition {
                name: source.clone(),
                level_params: vec![],
                type_,
                value: Expr::lam(
                    BinderInfo::Default,
                    u.clone(),
                    Expr::lam(BinderInfo::Default, u, Expr::bvar(1)),
                ),
                is_reducible: true,
            })
            .expect("a different same-name original definition is itself fully checked");
        let result =
            check_uint_source_value_equation(&module, function, &environment, &source, &proposed);
        assert!(
            matches!(result,Err(SourceValueEquationError::Rejected(ref message)) if message.contains("strict certification audit")),
            "{}: identical claimed goal must fail on its changed original definition",
            fixture.expected_source
        );
    }
}

#[path = "source_value_equation_producer/conditional.rs"]
mod conditional;

#[path = "source_value_equation_producer/fnv.rs"]
mod fnv;
