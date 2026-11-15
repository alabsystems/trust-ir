// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "clean-tv-anchor")]
//! Complete DATA from Clean's actual mixed scalar producer, independently
//! source-checked and replayed. No body, ABI, NoUB or executable permission.
use trust_ir::inst::ICmpOp;
use trust_ir::{FuncId, Inst, Module, Ty, ValueId};
use trust_ir_build::check_scalar_source_value_equation;
use trust_ir_build::clean_kernel::{
    BinderInfo, Declaration, DeclarationVerification, Environment, Expr, Name,
};

macro_rules! data {
    ($name:literal) => {
        include_bytes!(concat!(
            "fixtures/scalar_source_value_equations/",
            $name,
            ".json"
        )) as &[u8]
    };
}
struct Case {
    bytes: &'static [u8],
    source: Name,
    function: &'static str,
    parameters: Vec<Ty>,
    result: Ty,
}
fn cases() -> Vec<Case> {
    let mut cases = vec![Case {
        bytes: data!("rex_bool4_u8"),
        source: Name::from_string("actualRexSource"),
        function: "rex",
        parameters: vec![Ty::Bool; 4],
        result: Ty::U8,
    }];
    for (width, ty, extended, mixed) in [
        (
            8,
            Ty::U8,
            data!("extended_u8_bool"),
            data!("mixed_u8_bool_u8_bool"),
        ),
        (
            16,
            Ty::U16,
            data!("extended_u16_bool"),
            data!("mixed_u16_bool_u16_bool"),
        ),
        (
            32,
            Ty::U32,
            data!("extended_u32_bool"),
            data!("mixed_u32_bool_u32_bool"),
        ),
        (
            64,
            Ty::U64,
            data!("extended_u64_bool"),
            data!("mixed_u64_bool_u64_bool"),
        ),
    ] {
        cases.push(Case {
            bytes: extended,
            source: Name::from_string("actualExtendedSource").num(width),
            function: "extended",
            parameters: vec![ty.clone()],
            result: Ty::Bool,
        });
        cases.push(Case {
            bytes: mixed,
            source: Name::from_string("mixedOriginalSource").num(width),
            function: "mixed",
            parameters: vec![ty.clone(), Ty::Bool, ty.clone(), Ty::Bool],
            result: ty,
        });
    }
    cases
}
struct Fixture {
    module: Module,
    environment: Environment,
    definition: Declaration,
    theorem: Declaration,
    source_digest: [u8; 32],
    equation_digest: [u8; 32],
}
fn load(case: &Case) -> Fixture {
    assert!(case.bytes.len() <= 8 * 1024 * 1024);
    let data: serde_json::Value =
        serde_json::from_slice(case.bytes).expect("bounded complete DATA payload");
    assert_eq!(data["format"], "clean-scalar-original-source-data-v1");
    let module: Module =
        serde_json::from_value(data["module"].clone()).expect("complete actual module");
    assert_eq!(module.functions.len(), 1);
    let function = &module.functions[0];
    assert_eq!(function.id, FuncId::new(0));
    assert_eq!(function.name, case.function);
    let signature = &module.func_types[function.ty.as_usize()];
    assert_eq!(signature.params, case.parameters);
    assert_eq!(signature.returns, vec![case.result.clone()]);
    let definition: Declaration = serde_json::from_value(data["source_declaration"].clone())
        .expect("actual original definition");
    let Declaration::Definition {
        name, level_params, ..
    } = &definition
    else {
        panic!("original must be a definition")
    };
    assert_eq!(
        name, &case.source,
        "caller selects original identity independently of the producer theorem"
    );
    assert!(level_params.is_empty());
    let mut environment = Environment::with_prelude();
    environment
        .add_decl(definition.clone())
        .expect("independent full source kernel check");
    assert_eq!(
        environment.declaration_verification(&case.source),
        Some(DeclarationVerification::FullKernelCheck)
    );
    Fixture {
        module,
        environment,
        definition,
        theorem: serde_json::from_value(data["theorem"].clone())
            .expect("untrusted proposed theorem data"),
        source_digest: serde_json::from_value(data["source_closure_digest"].clone())
            .expect("source digest data"),
        equation_digest: serde_json::from_value(data["equation_closure_digest"].clone())
            .expect("equation digest data"),
    }
}

#[test]
fn actual_mixed_producer_equations_replay_with_independent_full_judgments() {
    for case in cases() {
        let f = load(&case);
        let checked = check_scalar_source_value_equation(
            &f.module,
            FuncId::new(0),
            &f.environment,
            &case.source,
            &f.theorem,
        )
        .expect(
            "consumer rederives actual mixed IR judgment and checks complete original-source proof",
        );
        assert_eq!(checked.source_closure_digest(), &f.source_digest);
        // Digest labels are consistency data: admit the EXACT original named
        // declaration independently before comparing its retained closure.
        let Declaration::Theorem { name, .. } = &f.theorem else {
            panic!("theorem")
        };
        let mut original_name_replay = f.environment.clone();
        original_name_replay
            .add_decl(f.theorem.clone())
            .expect("full kernel check under original theorem name");
        assert_eq!(
            original_name_replay.declaration_verification(name),
            Some(DeclarationVerification::FullKernelCheck)
        );
        assert_eq!(
            original_name_replay.closure_digest(name).unwrap(),
            f.equation_digest
        );
    }
}
fn carrier_name(ty: &Ty) -> &'static str {
    match ty {
        Ty::Bool => "Bool",
        Ty::U8 => "UInt8",
        Ty::U16 => "UInt16",
        Ty::U32 => "UInt32",
        Ty::U64 => "UInt64",
        _ => panic!("fixture carrier"),
    }
}
fn source_type(ty: &Ty) -> Expr {
    Expr::const_str(carrier_name(ty))
}

#[test]
fn actual_mixed_producer_proofs_refuse_changed_valid_source_and_bad_proofs() {
    for case in cases() {
        let f = load(&case);
        check_scalar_source_value_equation(
            &f.module,
            FuncId::new(0),
            &f.environment,
            &case.source,
            &f.theorem,
        )
        .unwrap();
        let mut wrong = f.theorem.clone();
        let Declaration::Theorem { value, .. } = &mut wrong else {
            panic!("theorem")
        };
        *value = Expr::const_str("Bool.true");
        assert!(
            check_scalar_source_value_equation(
                &f.module,
                FuncId::new(0),
                &f.environment,
                &case.source,
                &wrong
            )
            .is_err()
        );
        let mut zero = if case.result == Ty::Bool {
            Expr::const_str("Bool.false")
        } else {
            Expr::app(
                Expr::const_str(&format!("{}.ofNat", carrier_name(&case.result))),
                Expr::nat_lit(0),
            )
        };
        for parameter in case.parameters.iter().rev() {
            zero = Expr::lam(BinderInfo::Default, source_type(parameter), zero);
        }
        let mut changed_definition = f.definition.clone();
        let Declaration::Definition { value, .. } = &mut changed_definition else {
            panic!("definition")
        };
        *value = zero;
        let mut changed_environment = Environment::with_prelude();
        changed_environment
            .add_decl(changed_definition)
            .expect("changed source remains well typed");
        assert!(
            check_scalar_source_value_equation(
                &f.module,
                FuncId::new(0),
                &changed_environment,
                &case.source,
                &f.theorem
            )
            .is_err()
        );
    }
}
#[test]
fn actual_mixed_producer_ir_predicates_arms_and_hidden_bodies_are_bound() {
    for case in cases() {
        let f = load(&case);
        check_scalar_source_value_equation(
            &f.module,
            FuncId::new(0),
            &f.environment,
            &case.source,
            &f.theorem,
        )
        .unwrap();
        let mut changed = f.module.clone();
        let comparison = changed.functions[0].blocks[0]
            .body
            .iter_mut()
            .find(|n| matches!(n.inst, Inst::ICmp { .. }))
            .expect("actual comparison");
        let Inst::ICmp { op, .. } = &mut comparison.inst else {
            panic!("comparison")
        };
        *op = match op {
            ICmpOp::Eq => ICmpOp::Ne,
            ICmpOp::Ult => ICmpOp::Ule,
            _ => panic!("fixture predicate"),
        };
        assert!(
            check_scalar_source_value_equation(
                &changed,
                FuncId::new(0),
                &f.environment,
                &case.source,
                &f.theorem
            )
            .is_err()
        );
        let mut changed = f.module.clone();
        let choice = changed.functions[0].blocks[0]
            .body
            .iter_mut()
            .find(|n| matches!(n.inst, Inst::Select { .. }))
            .expect("actual selection");
        let Inst::Select {
            then_val, else_val, ..
        } = &mut choice.inst
        else {
            panic!("selection")
        };
        std::mem::swap(then_val, else_val);
        assert!(
            check_scalar_source_value_equation(
                &changed,
                FuncId::new(0),
                &f.environment,
                &case.source,
                &f.theorem
            )
            .is_err()
        );
        let mut changed = f.module.clone();
        let mut hidden = changed.functions[0].clone();
        hidden.id = FuncId::new(1);
        hidden.name = "invalid_unselected_helper".to_owned();
        let Inst::Return { values } = &mut hidden.blocks[0].body.last_mut().expect("return").inst
        else {
            panic!("return")
        };
        values[0] = ValueId::new(999);
        changed.functions.push(hidden);
        assert!(
            check_scalar_source_value_equation(
                &changed,
                FuncId::new(0),
                &f.environment,
                &case.source,
                &f.theorem
            )
            .is_err()
        );
    }
}
