// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::inst::{BinOp, CastOp};
use trust_ir::{
    Block, BlockId, DialectTy, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};
use trust_ir_build::validate::codegen_lowerability_errors;
use trust_ir_build::{ValidationError, validate_module, validate_module_for_codegen};

fn nominal(name: &str, version: u32) -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("example", name, version)))
}

fn module() -> Module {
    module_of(nominal("value", 1))
}

fn module_of(ty: Ty) -> Module {
    let mut module = Module::new("nominal_transport");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut helper = Function::new(FuncId::new(0), "helper", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), ty.clone());
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    helper.blocks.push(entry);
    module
        .try_add_function(helper)
        .expect("Module::try_add_function: test fixture");
    let mut caller = Function::new(FuncId::new(1), "caller", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), ty.clone());
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(1)],
    }));
    let mut join = Block::new(BlockId::new(1)).with_param(ValueId::new(2), ty.clone());
    join.body.push(
        InstrNode::new(Inst::Copy {
            ty,
            operand: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
    );
    join.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3)],
    }));
    caller.blocks = vec![join, entry];
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn nominal_values_use_ordinary_calls_cfg_parameters_and_copy() {
    assert_eq!(validate_module(&module()), vec![]);
}

#[test]
fn complete_result_typing_rejects_table_backed_and_legacy_call_result_laundering() {
    for element in [nominal("value", 1), Ty::I32] {
        let mut module = module_of(Ty::Array(trust_ir::TyId::new(0), 1));
        module.types.push(element);
        assert_eq!(validate_module(&module), vec![]);
        module.functions[1].blocks[1].body.insert(
            1,
            InstrNode::new(Inst::Copy {
                ty: Ty::I64,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(4)),
        );
        let errors = validate_module(&module);
        assert!(
            errors.iter().any(
                |e| matches!(e, ValidationError::OperandTypeMismatch { op, .. } if op == "copy")
            ),
            "{errors:?}"
        );
    }
}

#[test]
fn all_dialect_results_are_checked_by_existing_scalar_operand_rules() {
    let mut module = module_of(Ty::I64);
    let mut producer = InstrNode::new(Inst::DialectOp(Box::new(
        trust_ir::dialect::DialectInst::new("example", "pair")
            .with_result_ty(Ty::I64)
            .with_result_ty(Ty::Bool),
    )));
    producer.results = vec![ValueId::new(4), ValueId::new(5)];
    module.functions[1].blocks[1].body.insert(1, producer);
    module.functions[1].blocks[1].body.insert(
        2,
        InstrNode::new(Inst::Copy {
            ty: Ty::I64,
            operand: ValueId::new(5),
        })
        .with_result(ValueId::new(6)),
    );
    let errors = validate_module(&module);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::OperandTypeMismatch { op, .. } if op == "copy")),
        "{errors:?}"
    );
}

#[test]
fn table_backed_nominal_values_cannot_be_created_by_core_memory_operations() {
    let mut module = Module::new("nominal_load");
    module.types.push(nominal("value", 1));
    let ty = Ty::Array(trust_ir::TyId::new(0), 1);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "load", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Ptr);
    entry.body.push(
        InstrNode::new(Inst::Load {
            ty,
            ptr: ValueId::new(0),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    function.blocks.push(entry);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    assert!(
        validate_module(&module)
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidDialectType { .. }))
    );
    // An unrelated nominal table entry must not ban ordinary scalar memory.
    module.types[0] = Ty::I32;
    module.types.push(nominal("unused", 1));
    assert_eq!(validate_module(&module), vec![]);
}

#[test]
fn global_storage_cannot_hide_nominal_types_behind_raw_addresses() {
    for address in [
        Inst::GlobalAddr {
            global: trust_ir::value::GlobalId::new(0),
        },
        Inst::Const {
            ty: Ty::Ptr,
            value: trust_ir::Constant::SymbolAddr {
                symbol: "storage".into(),
                addend: 0,
            },
        },
    ] {
        let mut module = module_of(Ty::I64);
        module.types.push(nominal("value", 1));
        module.globals.push(trust_ir::Global {
            name: "storage".into(),
            ty: Ty::Array(trust_ir::TyId::new(0), 1),
            mutable: true,
            initializer: None,
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        });
        module.functions[1].blocks[1]
            .body
            .insert(1, InstrNode::new(address).with_result(ValueId::new(4)));
        assert!(validate_module(&module).iter().any(|e| matches!(e, ValidationError::InvalidDialectType { detail, .. } if detail.contains("globals"))));
        module.globals[0].ty = Ty::I64;
        assert_eq!(validate_module(&module), vec![]);
    }
}

#[test]
fn nominal_values_cannot_enter_untyped_variadic_argument_slots() {
    for ty in [
        nominal("value", 1),
        Ty::Array(trust_ir::TyId::new(0), 1),
        Ty::I64,
    ] {
        let should_reject = ty != Ty::I64;
        let mut module = module_of(ty);
        module.types.push(nominal("value", 1));
        module.target_info = Some(trust_ir::TargetInfo {
            triple: "x86_64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("sysv64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
        let sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: true,
            })
            .expect("Module::add_func_type: test fixture");
        let mut vararg = Function::new(FuncId::new(2), "variadic", sig, BlockId::new(0));
        vararg.linkage = trust_ir::Linkage::External;
        module
            .try_add_function(vararg)
            .expect("Module::try_add_function: test fixture");
        module.functions[1].blocks[1].body.insert(
            1,
            InstrNode::new(Inst::Call {
                callee: FuncId::new(2),
                args: vec![ValueId::new(1)],
            }),
        );
        let errors = validate_module(&module);
        if should_reject {
            assert!(errors.iter().any(|e| matches!(e, ValidationError::InvalidDialectType { detail, .. } if detail.contains("variadic"))), "{errors:?}");
        } else {
            assert_eq!(errors, vec![]);
        }
    }
}

#[test]
fn exact_typed_indirect_calls_can_transport_nominal_arguments_and_results() {
    let mut module = Module::new("semantic_indirect");
    let ty = nominal("value", 1);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Func(sig), ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "caller", caller_sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), Ty::Func(sig))
        .with_param(ValueId::new(1), ty);
    entry.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(0),
            sig,
            args: vec![ValueId::new(1)],
            calling_conv: trust_ir::CallingConv::C,
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    function.blocks.push(entry);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    assert_eq!(validate_module(&module), vec![]);
}

#[test]
fn implicit_nominal_call_results_do_not_hide_an_invalid_indirect_callee() {
    let mut module = Module::new("implicit_nominal_result");
    let ty = nominal("value", 1);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![ty],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "caller", caller_sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::I64);
    entry.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(0),
            sig,
            args: vec![],
            calling_conv: trust_ir::CallingConv::C,
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    function.blocks.push(entry);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    assert!(
        validate_module(&module)
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidDialectType { .. }))
    );
}

#[test]
fn symbolic_function_references_can_name_semantic_signatures_without_a_scalar_cast() {
    let mut module = module();
    let sig = module.functions[0].ty;
    module.functions[1].blocks[1].body.insert(
        1,
        InstrNode::new(Inst::Const {
            ty: Ty::Func(sig),
            value: trust_ir::Constant::FnDef(FuncId::new(0)),
        })
        .with_result(ValueId::new(4)),
    );
    module.functions[1].blocks[1].body.insert(
        2,
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(4),
            sig,
            args: vec![ValueId::new(0)],
            calling_conv: trust_ir::CallingConv::C,
        })
        .with_result(ValueId::new(5)),
    );
    assert_eq!(validate_module(&module), vec![]);
}

#[test]
fn call_results_cannot_launder_nominal_types_at_cfg_joins() {
    for wrong in [Ty::I64, nominal("different", 1), nominal("value", 2)] {
        let mut module = module();
        module.functions[1].blocks[0].params[0].1 = wrong;
        let errors = validate_module(&module);
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::BranchArgTypeMismatch { .. })),
            "{errors:?}"
        );
    }
}

#[test]
fn scalar_and_memory_operations_cannot_consume_nominal_call_results() {
    let value = ValueId::new(1);
    for inst in [
        Inst::Copy {
            ty: Ty::I64,
            operand: value,
        },
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::I64,
            dst_ty: Ty::I64,
            operand: value,
        },
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: value,
            rhs: value,
        },
        Inst::Load {
            ty: Ty::I64,
            ptr: value,
            volatile: false,
            align: None,
        },
        Inst::Copy {
            ty: nominal("value", 2),
            operand: value,
        },
    ] {
        let mut module = module();
        module.functions[1].blocks[1]
            .body
            .insert(1, InstrNode::new(inst).with_result(ValueId::new(4)));
        let errors = validate_module(&module);
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::InvalidDialectType { .. })),
            "{errors:?}"
        );
    }
}

#[test]
fn select_preserves_nominal_identity_and_requires_a_boolean_condition() {
    let mut module = module();
    module.functions[1].blocks[1].body.insert(
        1,
        InstrNode::new(Inst::Select {
            ty: nominal("value", 1),
            cond: ValueId::new(1),
            then_val: ValueId::new(1),
            else_val: ValueId::new(1),
        })
        .with_result(ValueId::new(4)),
    );
    assert!(
        validate_module(&module)
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidDialectType { .. }))
    );
    module.functions[1].blocks[1].body.insert(
        1,
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: trust_ir::Constant::Bool(true),
        })
        .with_result(ValueId::new(5)),
    );
    let Inst::Select { cond, .. } = &mut module.functions[1].blocks[1].body[2].inst else {
        unreachable!()
    };
    *cond = ValueId::new(5);
    assert_eq!(validate_module(&module), vec![]);
}

#[test]
fn nominal_call_results_are_not_indirect_function_pointers() {
    let mut module = module();
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.functions[1].blocks[1].body.insert(
        1,
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(1),
            sig,
            args: vec![],
            calling_conv: trust_ir::CallingConv::C,
        }),
    );
    assert!(
        validate_module(&module)
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidDialectType { .. }))
    );
}

#[test]
fn untrusted_nominal_identity_is_checked_even_in_unused_tables_and_type_attributes() {
    for identity in [
        DialectTy::new("", "value", 1),
        DialectTy::new("example", "bad.name", 1),
        DialectTy::new("example", "value", 0),
    ] {
        let mut module = module();
        module
            .types
            .push(Ty::Tuple(vec![Ty::Dialect(Box::new(identity.clone()))]));
        assert!(
            validate_module(&module)
                .iter()
                .any(|e| matches!(e, ValidationError::InvalidDialectType { .. }))
        );
        module.types.clear();
        module.functions[1].blocks[1].body.insert(
            1,
            InstrNode::new(Inst::DialectOp(Box::new(
                trust_ir::dialect::DialectInst::new("example", "marker").with_attr(
                    "type",
                    trust_ir::dialect::AttrValue::Ty(Ty::Dialect(Box::new(identity))),
                ),
            ))),
        );
        assert!(
            validate_module(&module)
                .iter()
                .any(|e| matches!(e, ValidationError::InvalidDialectType { .. }))
        );
    }
}

// ---------------------------------------------------------------------------
// WS2.20 (F-046): the dialect laundering path.
// ---------------------------------------------------------------------------

/// `caller(callee: callee_ty, arg: arg_ty) -> ret` whose body is ONE
/// `CallIndirect` through `callee` at signature `(arg_ty) -> ret`, returning
/// its result.
fn indirect_call_module(callee_ty: Option<Ty>, arg_ty: Ty, ret: Ty) -> Module {
    let mut module = Module::new("ws2_20_indirect");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![arg_ty.clone()],
            returns: vec![ret.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let callee_ty = callee_ty.unwrap_or(Ty::Func(sig));
    let caller_sig = module
        .add_func_type(FuncTy {
            params: vec![callee_ty.clone(), arg_ty.clone()],
            returns: vec![ret],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "caller", caller_sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), callee_ty)
        .with_param(ValueId::new(1), arg_ty);
    entry.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(0),
            sig,
            args: vec![ValueId::new(1)],
            calling_conv: trust_ir::CallingConv::C,
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    function.blocks.push(entry);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn is_origin_refusal(error: &ValidationError) -> bool {
    matches!(
        error,
        ValidationError::InvalidDialectType { detail, .. }
            if detail.contains("pointer-like indirect callee cannot originate a nominal dialect value")
    )
}

#[test]
fn ws2_20_exact_func_indirect_call_may_return_a_dialect_value() {
    // Positive fixture: the exact `Ty::Func` callee IS the signature, so the
    // dialect value it returns has an exact-typed origin.
    let ty = nominal("value", 1);
    let module = indirect_call_module(None, Ty::I64, ty);
    assert_eq!(validate_module(&module), vec![]);
}

#[test]
fn ws2_20_pointer_callee_cannot_originate_a_dialect_value() {
    // Negative twin: the same call through an untyped code address.
    for callee_ty in [
        Ty::Ptr,
        Ty::PtrConst(Box::new(Ty::U8)),
        Ty::PtrMut(Box::new(Ty::U8)),
    ] {
        let module = indirect_call_module(Some(callee_ty.clone()), Ty::I64, nominal("value", 1));
        let errors = validate_module(&module);
        assert!(
            errors.iter().any(is_origin_refusal),
            "{callee_ty}: {errors:?}"
        );
    }
}

#[test]
fn ws2_20_pointer_callee_cannot_originate_a_nested_dialect_value() {
    // The rule is REACHABILITY, not a bare-type match: a dialect value inside
    // a returned tuple is still an origin.
    let module = indirect_call_module(
        Some(Ty::Ptr),
        Ty::I64,
        Ty::Tuple(vec![Ty::I64, nominal("value", 1)]),
    );
    let errors = validate_module(&module);
    assert!(errors.iter().any(is_origin_refusal), "{errors:?}");
}

#[test]
fn ws2_20_mutation_control_pointer_callee_may_transport_a_dialect_argument() {
    // Scope pin: a pointer callee returning `u64` with a dialect-typed
    // ARGUMENT is transport, not an origin, and is unaffected by the rule.
    let module = indirect_call_module(Some(Ty::Ptr), nominal("value", 1), Ty::U64);
    assert_eq!(validate_module(&module), vec![]);
    // ...and flipping ONLY the return to a dialect type is what trips it.
    let module = indirect_call_module(Some(Ty::Ptr), nominal("value", 1), nominal("value", 1));
    assert!(validate_module(&module).iter().any(is_origin_refusal));
}

/// A body that makes a dialect-typed value with a `DialectOp` in `namespace`
/// and hands it to a function expecting exactly that type.
fn dialect_op_module(namespace: &str) -> Module {
    let ty = Ty::Dialect(Box::new(DialectTy::new("clean", "obj", 1)));
    let mut module = Module::new("ws2_20_dialect_op");
    let sink_sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let main_sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut sink = Function::new(FuncId::new(0), "sink", sink_sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), ty.clone());
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    sink.blocks.push(entry);
    module
        .try_add_function(sink)
        .expect("Module::try_add_function: test fixture");
    let mut main = Function::new(FuncId::new(1), "main", main_sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    let mut op = trust_ir::dialect::DialectInst::new(namespace, "make");
    op.result_tys.push(ty);
    entry
        .body
        .push(InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(ValueId::new(0)));
    entry.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(0)],
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    main.blocks.push(entry);
    module
        .try_add_function(main)
        .expect("Module::try_add_function: test fixture");
    module
}

fn unknown_namespace_refusals(errors: &[ValidationError], namespace: &str) -> usize {
    errors
        .iter()
        .filter(|error| {
            matches!(
                error,
                ValidationError::UnlowerableForCodegen { inst: "DialectOp", detail, .. }
                    if *detail == format!("unknown dialect namespace {namespace}: no registered lowering")
            )
        })
        .count()
}

#[test]
fn ws2_20_codegen_refuses_an_unknown_dialect_namespace() {
    // Codegen twin: `foo.bar` has no registered lowering.
    let mut module = dialect_op_module("foo");
    if let Inst::DialectOp(op) = &mut module.functions[1].blocks[0].body[0].inst {
        op.op = "bar".into();
    }
    assert_eq!(
        unknown_namespace_refusals(&codegen_lowerability_errors(&module), "foo"),
        1
    );
    assert_eq!(
        unknown_namespace_refusals(&validate_module_for_codegen(&module), "foo"),
        1
    );
    // Structural validation is unchanged: the op round-trips opaquely.
    assert_eq!(validate_module(&module), vec![]);
}

#[test]
fn ws2_20_codegen_admits_the_in_tree_dialect_namespaces() {
    // Mutation control for the namespace list: every in-tree decoded dialect
    // passes the namespace check (its op-level decode is the structural
    // validator's job), and the check is exact — a case variant is unknown.
    for namespace in ["vector", "gpu", "avx512", "ane", "trust_rust"] {
        let module = dialect_op_module(namespace);
        assert_eq!(
            unknown_namespace_refusals(&codegen_lowerability_errors(&module), namespace),
            0,
            "{namespace}"
        );
    }
    let module = dialect_op_module("Vector");
    assert_eq!(
        unknown_namespace_refusals(&codegen_lowerability_errors(&module), "Vector"),
        1
    );
}

/// Ported GAP row `trust-ir-self-declared/dialect-laundering-path`: a
/// `DialectOp` in namespace `evil` producing a `Ty::Dialect{clean,obj,1}`
/// value, passed to a function expecting that type. `validate_module` still
/// accepts it (opaque round-trip is the ratified structural contract), but
/// the codegen entry point refuses it by name, and the other half of the
/// laundering path — re-originating the value through a pointer-like
/// indirect callee — is refused structurally.
#[test]
fn trust_ir_self_declared_dialect_laundering_path() {
    let module = dialect_op_module("evil");
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(
        unknown_namespace_refusals(&validate_module_for_codegen(&module), "evil"),
        1
    );
    let laundered = indirect_call_module(
        Some(Ty::Ptr),
        Ty::I64,
        Ty::Dialect(Box::new(DialectTy::new("clean", "obj", 1))),
    );
    assert!(validate_module(&laundered).iter().any(is_origin_refusal));
}

// ---------------------------------------------------------------------------
// WS2.20 review: adversarial shapes the first cut did not pin.
// ---------------------------------------------------------------------------

#[test]
fn ws2_20_review_pointer_callee_cannot_originate_a_table_backed_dialect_value() {
    // The dialect sits behind a NAMED type-table entry (`[types[2]; 1]`), not
    // inline, so a bare inline match on the return would miss it.
    let mut module =
        indirect_call_module(Some(Ty::Ptr), Ty::I64, Ty::Array(trust_ir::TyId::new(0), 1));
    module.types.push(nominal("value", 1));
    let errors = validate_module(&module);
    assert!(errors.iter().any(is_origin_refusal), "{errors:?}");
    // Control: the same table entry naming a scalar is ordinary.
    module.types[0] = Ty::I32;
    assert_eq!(validate_module(&module), vec![]);
}

#[test]
fn ws2_20_review_pointer_callee_cannot_originate_a_function_value_that_returns_a_dialect() {
    // Two-step laundering: an untyped code address returns an EXACT
    // `Ty::Func(minter)` whose signature returns a dialect value; a second,
    // exact-typed `CallIndirect` through it would then be admitted. The first
    // step is already an origin — the function type reaches the dialect.
    let mut module =
        indirect_call_module(Some(Ty::Ptr), Ty::I64, Ty::Func(trust_ir::FuncTyId::new(2)));
    let minter = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![nominal("value", 1)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert_eq!(minter.index(), 2);
    let errors = validate_module(&module);
    assert!(errors.iter().any(is_origin_refusal), "{errors:?}");
}

#[test]
fn ws2_20_review_mismatched_func_and_fat_callees_are_pointer_like_origins() {
    // `Ty::Func(other)` with `other != sig` is NOT the exact callee: it is a
    // pointer-like code address whose own signature returns no dialect, called
    // at a signature that does. So is a fat pointer. Both are refused as
    // origins, not admitted as transport.
    let mut module = indirect_call_module(
        Some(Ty::Func(trust_ir::FuncTyId::new(2))),
        Ty::I64,
        nominal("value", 1),
    );
    module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let errors = validate_module(&module);
    assert!(errors.iter().any(is_origin_refusal), "{errors:?}");

    let module = indirect_call_module(
        Some(Ty::FatPtr(trust_ir::FatPtrKind::Str)),
        Ty::I64,
        nominal("value", 1),
    );
    let errors = validate_module(&module);
    assert!(errors.iter().any(is_origin_refusal), "{errors:?}");
}

#[test]
fn ws2_20_review_missing_signature_fails_closed_under_the_origin_rule() {
    // A dialect ARGUMENT through a pointer callee is transport only when the
    // signature can be read; a dangling `sig` cannot prove it returns no
    // dialect, so the node is refused as an origin (beside the sig error).
    let mut module = indirect_call_module(Some(Ty::Ptr), nominal("value", 1), Ty::U64);
    assert_eq!(validate_module(&module), vec![]);
    if let Inst::CallIndirect { sig, .. } = &mut module.functions[0].blocks[0].body[0].inst {
        *sig = trust_ir::FuncTyId::new(99);
    }
    let errors = validate_module(&module);
    assert!(errors.iter().any(is_origin_refusal), "{errors:?}");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::CallIndirectSigNotFound { sig_id: 99, .. }
        )),
        "{errors:?}"
    );
}

#[test]
fn ws2_20_review_codegen_refuses_an_unknown_namespace_without_any_nominal_type() {
    // Rule 2 is about the NAMESPACE, not the type: a `foo.nop` producing a
    // plain `i32` in a module with no `Ty::Dialect` anywhere is refused too.
    let mut module = Module::new("ws2_20_scalar_dialect_op");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut main = Function::new(FuncId::new(0), "main", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    let mut op = trust_ir::dialect::DialectInst::new("foo", "nop");
    op.result_tys.push(Ty::I32);
    entry
        .body
        .push(InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(ValueId::new(0)));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    main.blocks.push(entry);
    module
        .try_add_function(main)
        .expect("Module::try_add_function: test fixture");
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(
        unknown_namespace_refusals(&codegen_lowerability_errors(&module), "foo"),
        1
    );
}
