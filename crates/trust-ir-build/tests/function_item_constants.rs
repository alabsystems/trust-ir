// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::ty::{
    ClosureTy, EnumDef, EnumVariant, FieldDef, RecordDef, SetRepr, StructDef, StructRepr,
};
use trust_ir::value::{EnumId, RecordId, StructId};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage, Module,
    Ty, ValueId,
};
use trust_ir_build::{ValidationError, validate_module};

const TARGET: FuncId = FuncId::new(100_003);

fn fixture(container: usize, wrong_target: bool, wrong_signature: bool, global: bool) -> Module {
    let mut module = Module::new("function_item_identity");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let other_signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut target = Function::new(TARGET, "target", signature, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    target.blocks.push(entry);
    module
        .try_add_function(target)
        .expect("Module::try_add_function: test fixture");
    let ty = Ty::Func(if wrong_signature {
        other_signature
    } else {
        signature
    });
    let value = Constant::FnDef(if wrong_target {
        FuncId::new(999_999)
    } else {
        TARGET
    });
    let field = |ty| FieldDef {
        name: "callback".into(),
        ty,
        offset: None,
    };
    let (ty, value) = match container {
        0 => (ty, value),
        1 => (Ty::Tuple(vec![ty]), Constant::Aggregate(vec![value])),
        2 => (
            Ty::Array(
                module.add_type(ty).expect("Module::add_type: test fixture"),
                1,
            ),
            Constant::Array(vec![value]),
        ),
        3 => (
            Ty::Sequence(module.add_type(ty).expect("Module::add_type: test fixture")),
            Constant::Sequence(vec![value]),
        ),
        4 => (
            Ty::Set(
                module.add_type(ty).expect("Module::add_type: test fixture"),
                SetRepr::Boxed,
            ),
            Constant::Set(vec![value]),
        ),
        5 => {
            let id = module.add_record(RecordDef {
                id: RecordId::new(0),
                name: "Callbacks".into(),
                fields: vec![field(ty)],
            });
            (
                Ty::Record(id),
                Constant::Record(vec![("callback".into(), value)]),
            )
        }
        6 => {
            let id = module.add_struct(StructDef {
                id: StructId::new(0),
                name: "Callbacks".into(),
                fields: vec![field(ty)],
                size: None,
                align: None,
                repr: StructRepr::Rust,
                origin: None,
            });
            (Ty::Struct(id), Constant::Aggregate(vec![value]))
        }
        7 => {
            let id = module.add_enum(EnumDef::new(
                EnumId::new(0),
                "Callback",
                vec![EnumVariant {
                    name: "Some".into(),
                    fields: vec![ty],
                    field_names: vec![],
                }],
            ));
            (
                Ty::Enum(id),
                Constant::Aggregate(vec![Constant::Int(0), value]),
            )
        }
        8 => {
            let id = module
                .add_closure_type(ClosureTy {
                    func: signature,
                    captures: vec![ty],
                })
                .expect("Module::add_closure_type: test fixture");
            (
                Ty::Closure(id),
                Constant::Closure {
                    func: TARGET,
                    captures: vec![value],
                },
            )
        }
        _ => unreachable!(),
    };
    if global {
        module.globals.push(Global {
            name: "callbacks".into(),
            ty,
            mutable: false,
            initializer: Some(value),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        });
    } else {
        let mut caller = Function::new(FuncId::new(7), "holder", signature, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry
            .body
            .push(InstrNode::new(Inst::Const { ty, value }).with_result(ValueId::new(0)));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        caller.blocks.push(entry);
        module
            .try_add_function(caller)
            .expect("Module::try_add_function: test fixture");
    }
    module
}

#[test]
fn function_items_are_checked_without_any_indirect_call_in_every_typed_container() {
    for container in 0..9 {
        for global in [false, true] {
            let control = fixture(container, false, false, global);
            assert_eq!(
                validate_module(&control),
                vec![],
                "control container {container}, global {global}"
            );
            for (wrong_target, wrong_signature) in [(true, false), (false, true)] {
                let errors =
                    validate_module(&fixture(container, wrong_target, wrong_signature, global));
                assert!(
                    errors
                        .iter()
                        .any(|error| matches!(error, ValidationError::ConstTypeMismatch { .. })),
                    "container {container}, global {global}, wrong_target {wrong_target}: {errors:?}"
                );
            }
        }
    }
}

#[test]
fn ambiguous_function_identity_cannot_be_materialized() {
    let mut module = fixture(0, false, false, false);
    let mut duplicate = module.functions[0].clone();
    duplicate.name = "duplicate".into();
    module.functions.push(duplicate);
    assert!(validate_module(&module).iter().any(|error| matches!(error,
        ValidationError::ConstTypeMismatch { actual, .. } if actual.contains("ambiguous"))));
}

#[test]
fn function_items_remain_nominal_in_their_declared_signature_id() {
    let mut module = fixture(0, false, false, false);
    let duplicate_signature = module
        .add_func_type(module.func_types[0].clone())
        .expect("Module::add_func_type: test fixture");
    let Inst::Const { ty, .. } = &mut module.functions[1].blocks[0].body[0].inst else {
        unreachable!()
    };
    *ty = Ty::Func(duplicate_signature);
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::ConstTypeMismatch { .. }))
    );
}

#[test]
fn deep_constant_descent_is_stack_safe_and_does_not_copy_diagnostic_prefixes() {
    for (depth, container, wrong_target) in [
        (20_000, 0, false),
        (20_000, 0, true),
        (10_000, 1, true),
        (20_000, 2, false),
        (20_000, 2, true),
    ] {
        let mut module = fixture(0, wrong_target, false, false);
        let Inst::Const { ty, value } = &mut module.functions[1].blocks[0].body[0].inst else {
            unreachable!()
        };
        let mut ty = ty.clone();
        let mut value = std::mem::replace(value, Constant::PhantomData);
        for _ in 0..depth {
            if container == 1 {
                let id = module
                    .add_closure_type(ClosureTy {
                        func: module.functions[0].ty,
                        captures: vec![ty],
                    })
                    .expect("Module::add_closure_type: test fixture");
                ty = Ty::Closure(id);
                value = Constant::Closure {
                    func: TARGET,
                    captures: vec![value],
                };
            } else if container == 0 {
                ty = Ty::Sequence(module.add_type(ty).expect("Module::add_type: test fixture"));
                value = Constant::Sequence(vec![value]);
            } else {
                ty = Ty::Array(
                    module.add_type(ty).expect("Module::add_type: test fixture"),
                    1,
                );
                value = Constant::Array(vec![value]);
            }
        }
        module.functions[1].blocks[0].body[0].inst = Inst::Const { ty, value };
        // Drop, serde and parsing of arbitrary-depth recursive Rust data are
        // separate contracts. This regression exercises public validation only.
        let module = Box::leak(Box::new(module));
        let errors = validate_module(module);
        if wrong_target {
            assert!(
                errors.iter().any(
                    |error| matches!(error, ValidationError::ConstTypeMismatch { actual, .. }
                if actual.contains("missing or ambiguous"))
                ),
                "deep leaf must be reached"
            );
        } else {
            assert!(errors.is_empty(), "valid deep function item: {errors:?}");
        }
    }
}

#[test]
fn cyclic_container_types_terminate_by_consuming_real_constant_children() {
    let mut module = fixture(0, false, false, false);
    let recursive = module
        .add_type(Ty::Sequence(trust_ir::TyId::new(0)))
        .expect("Module::add_type: test fixture");
    let mut value = Constant::Sequence(vec![]);
    for _ in 0..10_000 {
        value = Constant::Sequence(vec![value]);
    }
    module.functions[1].blocks[0].body[0].inst = Inst::Const {
        ty: Ty::Sequence(recursive),
        value,
    };
    let module = Box::leak(Box::new(module));
    assert_eq!(validate_module(module), vec![]);
}

#[test]
fn wide_sibling_containers_check_the_last_function_item_without_a_width_sized_worklist() {
    let mut module = fixture(0, false, false, false);
    let signature = module.functions[0].ty;
    let element = module
        .add_type(Ty::Func(signature))
        .expect("Module::add_type: test fixture");
    let mut values = vec![Constant::FnDef(TARGET); 20_000];
    *values.last_mut().unwrap() = Constant::FnDef(FuncId::new(999_999));
    module.functions[1].blocks[0].body[0].inst = Inst::Const {
        ty: Ty::Sequence(element),
        value: Constant::Sequence(values),
    };
    assert!(validate_module(&module).iter().any(|error| matches!(error,
        ValidationError::ConstTypeMismatch { location, .. } if location.ends_with("[19999]"))));
}

#[test]
fn nested_closure_container_arity_and_type_must_be_valid_before_capture_typing() {
    for container in 0..3 {
        for failure in 0..4 {
            let mut module = fixture(8, false, false, false);
            let Inst::Const { ty, value } = &mut module.functions[1].blocks[0].body[0].inst else {
                unreachable!()
            };
            let mut ty = ty.clone();
            let mut value = std::mem::replace(value, Constant::PhantomData);
            let Constant::Closure { captures, .. } = &mut value else {
                unreachable!()
            };
            match failure {
                0 => {} // Valid nested closure control.
                1 => captures.push(Constant::FnDef(FuncId::new(999_999))),
                2 => captures.clear(),
                _ => module.closure_types.clear(),
            }
            match container {
                0 => {
                    ty = Ty::Sequence(module.add_type(ty).expect("Module::add_type: test fixture"));
                    value = Constant::Sequence(vec![value]);
                }
                1 => {
                    ty = Ty::Array(
                        module.add_type(ty).expect("Module::add_type: test fixture"),
                        1,
                    );
                    value = Constant::Array(vec![value]);
                }
                _ => {
                    ty = Ty::Tuple(vec![ty]);
                    value = Constant::Aggregate(vec![value]);
                }
            }
            module.functions[1].blocks[0].body[0].inst = Inst::Const { ty, value };
            let errors = validate_module(&module);
            if failure == 0 {
                assert_eq!(errors, vec![], "valid nested closure {container}");
            } else if failure == 3 {
                assert!(errors.iter().any(|error| matches!(error, ValidationError::ConstTypeReferenceNotFound { type_ref, .. }
                    if type_ref.starts_with("closure."))), "nested missing type {container}: {errors:?}");
            } else {
                assert!(
                    errors.iter().any(
                        |error| matches!(error, ValidationError::ConstTypeMismatch { expected, .. }
                    if expected.contains("captures for closure."))
                    ),
                    "nested arity {container}/{failure}: {errors:?}"
                );
            }
        }
    }
}
