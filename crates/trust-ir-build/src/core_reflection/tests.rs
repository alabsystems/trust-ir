// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ModuleBuilder;
use clean_kernel::ExprKind;
use trust_ir::{
    BinOp, Endianness, FieldDef, ICmpOp, Linkage, StructDef, StructId, StructPassingPolicy,
    StructRepr, TargetInfo,
};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

// This uses the real builder to construct the native TY calling/closure shape,
// not certificate-supplied Expr meanings. Execution is a separate Clean test.
fn native_shape() -> Module {
    let mut module = ModuleBuilder::new_with_target_info("actual_core_fixture", target());
    let pair = module.add_struct(StructDef {
        id: StructId(0),
        name: "HelperResult".into(),
        fields: vec![
            FieldDef {
                name: "status".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "payload".into(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    });
    let byte = module.add_type(Ty::U8);
    let helper_sig = module.add_func_type(vec![Ty::Ptr], vec![Ty::Struct(pair)]);
    let helper = module.declare_function("runtime_helper", helper_sig);
    let returns = vec![Ty::Ptr, Ty::U64, Ty::I64, Ty::U64, Ty::U64];
    let local_sig = module.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr], returns);
    let leaf = module.declare_function("leaf", local_sig);
    let entry = module.declare_function("entry", local_sig);
    {
        let mut b = module.define_function(leaf).expect("reserved leaf");
        b.set_calling_conv(CallingConv::Fast);
        let start = b.create_block();
        let _context = b.add_block_param(start, Ty::Ptr);
        let state = b.add_block_param(start, Ty::Ptr);
        let _environment = b.add_block_param(start, Ty::Ptr);
        b.switch_to_block(start);
        let status = b.uconst(Ty::U64, 0);
        let value = b.iconst(Ty::I64, -1);
        let unknown = b.uconst(Ty::U64, u64::MAX.into());
        let _wide = b.uconst(Ty::U128, u128::MAX);
        b.ret(vec![state, status, value, unknown, unknown]);
        b.build();
    }
    {
        let mut b = module.define_function(entry).expect("reserved entry");
        b.set_calling_conv(CallingConv::Fast);
        let start = b.create_block();
        let context = b.add_block_param(start, Ty::Ptr);
        let state = b.add_block_param(start, Ty::Ptr);
        let _environment = b.add_block_param(start, Ty::Ptr);
        let yes = b.create_block();
        let no = b.create_block();
        let exit = b.create_block();
        let exit_value = b.add_block_param(exit, Ty::I64);
        b.switch_to_block(start);
        let frame = b.alloca_aligned(Ty::Array(byte, 32), 8);
        let code_slot = b.gep_byte_offset(frame, 0);
        let capture_slot = b.gep_byte_offset(frame, 8);
        let function = b.fn_addr(local_sig, leaf);
        let null = b.null_ptr();
        b.store_aligned(Ty::Func(local_sig), code_slot, function, 8);
        b.store(Ty::Ptr, capture_slot, null);
        let callback = b.load(Ty::Func(local_sig), code_slot);
        let capture = b.load(Ty::Ptr, capture_slot);
        let direct = b.call_results::<5>(leaf, vec![context, state, capture]);
        let indirect = b.call_indirect_results_cc::<5>(
            callback,
            local_sig,
            vec![context, direct[0], capture],
            CallingConv::Fast,
        );
        let helper_result = b.call(helper, vec![context]);
        let status = b.extract_field(Ty::U64, helper_result, 0);
        let payload = b.extract_field(Ty::I64, helper_result, 1);
        let zero = b.uconst(Ty::U64, 0);
        let ok = b.icmp(ICmpOp::Eq, Ty::U64, status, zero);
        let selected = b.select(Ty::I64, ok, payload, indirect[2]);
        b.condbr(ok, yes, vec![], no, vec![]);
        b.switch_to_block(yes);
        b.br(exit, vec![selected]);
        b.switch_to_block(no);
        b.br(exit, vec![indirect[2]]);
        b.switch_to_block(exit);
        b.ret(vec![
            indirect[0],
            status,
            exit_value,
            indirect[3],
            indirect[4],
        ]);
        b.build();
    }
    let mut module = module.build().expect("ModuleBuilder::build: test fixture");
    for function in &mut module.functions {
        if function.calling_conv == CallingConv::Fast {
            function.linkage = Linkage::Internal;
        }
    }
    assert!(
        crate::validate_module(&module).is_empty(),
        "fixture must be actual valid Core"
    );
    module
}

fn addresses(module: &Module) -> Vec<(FuncId, u64)> {
    module
        .functions
        .iter()
        .map(|f| (f.id, 4096 + u64::from(f.id.0) * 16))
        .collect()
}

fn args<'a>(term: &'a Expr, expected: &str) -> Vec<&'a Expr> {
    let mut head = term;
    let mut arguments = Vec::new();
    while let ExprKind::App(function, argument) = head.kind() {
        arguments.push(argument.as_ref());
        head = function;
    }
    assert_eq!(*head, c(expected), "unexpected reflected constructor");
    arguments.reverse();
    arguments
}

fn elements(term: &Expr) -> Vec<&Expr> {
    let mut cursor = term;
    let mut out = Vec::new();
    loop {
        if *cursor.get_app_fn() == c("IRList.nil") {
            assert_eq!(args(cursor, "IRList.nil").len(), 1);
            return out;
        }
        let fields = args(cursor, "IRList.cons");
        assert_eq!(fields.len(), 3);
        out.push(fields[1]);
        cursor = fields[2];
    }
}

fn context(module: &Module) -> Expr {
    reflect_core_module_v1(module, &addresses(module))
        .expect("actual Core reflection")
        .context_term()
        .clone()
}

#[test]
fn minimal_return_context_matches_frozen_constructor_term() {
    let mut builder = ModuleBuilder::new_with_target_info("lookup_context_golden", target());
    let signature = builder.add_func_type(vec![], vec![]);
    let function = builder.declare_function("entry", signature);
    let mut body = builder.define_function(function).unwrap();
    body.set_calling_conv(CallingConv::C);
    let block = body.create_block();
    body.switch_to_block(block);
    body.ret(vec![]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    // Frozen on the pre-index reflector: includes every context component and
    // the real fetched Return node/site. Raw lookup indexes must add NO fields
    // or reorder any list in the reflected execution vocabulary.
    let expected_node = app(
        "IRNode.mk",
        [app("IRInst.ret", [list("Nat", [])]), list("Nat", [])],
    );
    let expected_block = app(
        "IRBlock.mk",
        [nat(0), list("Nat", []), list("IRNode", [expected_node])],
    );
    let expected_function = app(
        "IRFunc.mk",
        [
            nat(0),
            list("Nat", []),
            nat(0),
            list("IRBlock", [expected_block]),
        ],
    );
    let expected = app(
        "IRByteContextV1.mk",
        [
            app(
                "IRModule.mk",
                [list("IRFunc", [expected_function]), list("IRGlobal", [])],
            ),
            list("IRByteLayoutV1", []),
            list(
                "IRByteSignatureV1",
                [app(
                    "IRByteSignatureV1.mk",
                    [nat(0), list("IRTy", []), list("IRTy", []), boolean(false)],
                )],
            ),
            list(
                "IRByteFunctionV1",
                [app(
                    "IRByteFunctionV1.mk",
                    [nat(0), nat(0), nat(4096), nat(0), boolean(false)],
                )],
            ),
            list(
                "IRByteSiteV1",
                [app(
                    "IRByteSiteV1.mk",
                    [nat(0), nat(0), nat(0), nat(0), nat(0), list("IRTy", [])],
                )],
            ),
        ],
    );
    let actual = context(&module);
    assert_eq!(actual, expected);
    #[cfg(feature = "clean-tv-anchor")]
    assert_eq!(
        trust_ir::proof::encode_clean_expr_v1(&actual).unwrap(),
        trust_ir::proof::encode_clean_expr_v1(&expected).unwrap(),
    );
}

fn nodes(context: &Expr) -> Vec<&Expr> {
    let context = args(context, "IRByteContextV1.mk");
    let module = args(context[0], "IRModule.mk");
    elements(module[0])
        .into_iter()
        .flat_map(|function| {
            let function = args(function, "IRFunc.mk");
            elements(function[3])
                .into_iter()
                .flat_map(|block| {
                    let block = args(block, "IRBlock.mk");
                    elements(block[2])
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

#[test]
fn actual_integer_binary_module_preserves_opcode_type_operands_and_result_id() {
    let operators = [
        (BinOp::Add, "add"),
        (BinOp::Sub, "sub"),
        (BinOp::Mul, "mul"),
        (BinOp::UDiv, "udiv"),
        (BinOp::SDiv, "sdiv"),
        (BinOp::URem, "urem"),
        (BinOp::SRem, "srem"),
        (BinOp::And, "and_"),
        (BinOp::Or, "or_"),
        (BinOp::Xor, "xor_"),
        (BinOp::Shl, "shl"),
        (BinOp::LShr, "lshr"),
        (BinOp::AShr, "ashr"),
    ];
    for (ty, constructor, width) in [
        (Ty::I8, "IRTy.int_", 8),
        (Ty::U16, "IRTy.uint_", 16),
        (Ty::I32, "IRTy.int_", 32),
        (Ty::U64, "IRTy.uint_", 64),
        (Ty::I128, "IRTy.int_", 128),
        (Ty::U128, "IRTy.uint_", 128),
    ] {
        let mut builder = ModuleBuilder::new_with_target_info("integer_operators", target());
        let signature = builder.add_func_type(
            vec![ty.clone(), ty.clone()],
            vec![ty.clone(); operators.len()],
        );
        let function = builder.declare_function("binary", signature);
        let mut body = builder.define_function(function).unwrap();
        let block = body.create_block();
        let left = body.add_block_param(block, ty.clone());
        let right = body.add_block_param(block, ty.clone());
        body.switch_to_block(block);
        let mut expected = Vec::new();
        for (index, (op, name)) in operators.iter().enumerate() {
            // Keep noncommutative operand order observable, including a
            // repeated operand. Reflection must not normalize syntax away.
            let (a, b) = match index % 3 {
                0 => (left, right),
                1 => (right, left),
                _ => (right, right),
            };
            let result = body.binop(*op, ty.clone(), a, b);
            expected.push((*name, a, b, result));
        }
        body.ret(expected.iter().map(|(_, _, _, value)| *value).collect());
        body.build();
        let module = builder.build().expect("ModuleBuilder::build: test fixture");
        assert!(crate::validate_module(&module).is_empty());
        let reflected = context(&module);
        let actual = nodes(&reflected);
        assert_eq!(actual.len(), operators.len() + 1);
        for (node, (op, a, b, result)) in actual.iter().zip(expected) {
            let fields = args(node, "IRNode.mk");
            assert_eq!(
                *fields[0],
                app(
                    "IRInst.binop",
                    [
                        c(&format!("IRBinOp.{op}")),
                        app(constructor, [nat(width)]),
                        nat(u64::from(a.0)),
                        nat(u64::from(b.0)),
                    ]
                )
            );
            assert_eq!(elements(fields[1]), vec![&nat(u64::from(result.0))]);
        }
    }
}

#[test]
fn actual_boolean_binary_spellings_preserve_canonical_type_operands_and_results() {
    let operators = [
        (BinOp::And, "and_"),
        (BinOp::Or, "or_"),
        (BinOp::Xor, "xor_"),
        (BinOp::BAnd, "and_"),
        (BinOp::BOr, "or_"),
        (BinOp::BXor, "xor_"),
    ];
    for (op, canonical) in operators {
        let mut builder = ModuleBuilder::new_with_target_info("boolean_operators", target());
        let signature = builder.add_func_type(vec![Ty::Bool; 2], vec![Ty::Bool; 3]);
        let function = builder.declare_function("binary", signature);
        let mut body = builder.define_function(function).unwrap();
        let block = body.create_block();
        let left = body.add_block_param(block, Ty::Bool);
        let right = body.add_block_param(block, Ty::Bool);
        body.switch_to_block(block);
        let mut expected = Vec::new();
        // These operators commute semantically, but reflection must still
        // preserve exact source operand order, aliasing and destination IDs.
        for (lhs, rhs) in [(left, right), (right, left), (right, right)] {
            let result = body.binop(op, Ty::Bool, lhs, rhs);
            expected.push((lhs, rhs, result));
        }
        body.ret(expected.iter().map(|(_, _, result)| *result).collect());
        body.build();
        let module = builder.build().expect("ModuleBuilder::build: test fixture");
        assert!(crate::validate_module(&module).is_empty(), "{op:?}");
        let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
        assert!(std::ptr::eq(reflected.module(), &module));
        let actual = nodes(reflected.context_term());
        assert_eq!(actual.len(), expected.len() + 1);
        for (node, (lhs, rhs, result)) in actual.iter().zip(&expected) {
            let fields = args(node, "IRNode.mk");
            assert_eq!(
                *fields[0],
                app(
                    "IRInst.binop",
                    [
                        c(&format!("IRBinOp.{canonical}")),
                        c("IRTy.bool_"),
                        nat(u64::from(lhs.0)),
                        nat(u64::from(rhs.0)),
                    ]
                ),
                "{op:?} must not turn Bool into an integer carrier"
            );
            assert_eq!(elements(fields[1]), vec![&nat(u64::from(result.0))]);
        }
        let ctx = args(reflected.context_term(), "IRByteContextV1.mk");
        let signatures = elements(ctx[2]);
        assert_eq!(signatures.len(), 1);
        let signature = args(signatures[0], "IRByteSignatureV1.mk");
        assert_eq!(elements(signature[1]), vec![&c("IRTy.bool_"); 2]);
        assert_eq!(elements(signature[2]), vec![&c("IRTy.bool_"); 3]);
        let sites = elements(ctx[4]);
        assert_eq!(sites.len(), actual.len());
        for site in &sites[..expected.len()] {
            let site = args(site, "IRByteSiteV1.mk");
            assert_eq!(elements(site[5]), vec![&c("IRTy.bool_")]);
        }
    }
}

fn binary_type_fixture(op: BinOp, ty: Ty) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info("binary_type_fixture", target());
    let signature = builder.add_func_type(vec![ty.clone(); 2], vec![ty.clone()]);
    let function = builder.declare_function("binary", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let left = body.add_block_param(block, ty.clone());
    let right = body.add_block_param(block, ty.clone());
    body.switch_to_block(block);
    let result = body.binop(op, ty, left, right);
    body.ret(vec![result]);
    body.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn boolean_only_binary_spellings_reject_integer_types_before_reflection() {
    for op in [BinOp::BAnd, BinOp::BOr, BinOp::BXor] {
        for ty in [
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::I64,
            Ty::I128,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::U128,
        ] {
            let module = binary_type_fixture(op, ty.clone());
            let errors = crate::validate_module(&module);
            assert!(
                errors
                    .iter()
                    .any(|error| matches!(error, crate::ValidationError::BinOpRequiresBool { .. })),
                "{op:?} on {ty:?}: {errors:?}"
            );
            let error = reflect_core_module_v1(&module, &addresses(&module)).unwrap_err();
            assert!(error.to_string().contains("invalid actual Core module"));
        }
    }
}

#[test]
fn boolean_binary_operand_and_result_type_drift_is_rejected() {
    for op in [
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::BAnd,
        BinOp::BOr,
        BinOp::BXor,
    ] {
        let baseline = binary_type_fixture(op, Ty::Bool);
        assert!(crate::validate_module(&baseline).is_empty());
        for mutation in 0..4 {
            let mut module = baseline.clone();
            match mutation {
                // Keep entry/signature consistency so the actual binary
                // operand check, not an unrelated entry error, rejects this.
                0 | 1 => {
                    module.func_types[0].params[mutation] = Ty::U8;
                    module.functions[0].blocks[0].params[mutation].1 = Ty::U8;
                }
                // Return type is independent of the instruction's Bool result.
                2 => module.func_types[0].returns[0] = Ty::U8,
                // The instruction itself declares its result type; changing
                // it must not silently relabel the existing Bool operands.
                _ => match &mut module.functions[0].blocks[0].body[0].inst {
                    Inst::BinOp { ty, .. } => *ty = Ty::U8,
                    _ => unreachable!("fixture begins with the actual binary operation"),
                },
            }
            assert!(
                !crate::validate_module(&module).is_empty(),
                "{op:?}, mutation {mutation}"
            );
            let error = reflect_core_module_v1(&module, &addresses(&module)).unwrap_err();
            assert!(
                error.to_string().contains("invalid actual Core module"),
                "{op:?}, mutation {mutation}: {error}"
            );
        }
    }
}

#[test]
fn well_typed_boolean_vectors_remain_unsupported_by_byte_reflection() {
    for op in [
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::BAnd,
        BinOp::BOr,
        BinOp::BXor,
    ] {
        for lanes in [1, 4] {
            let module = binary_type_fixture(op, Ty::Vector(Box::new(Ty::Bool), lanes));
            let errors = crate::validate_module(&module);
            assert!(errors.is_empty(), "{op:?}, lanes {lanes}: {errors:?}");
            let error = reflect_core_module_v1(&module, &addresses(&module)).unwrap_err();
            assert!(
                error.to_string().contains("unsupported byte-profile type"),
                "{op:?}, lanes {lanes}: {error}"
            );
        }
    }
}

#[test]
fn actual_module_reflects_all_fourteen_native_operations_and_full_result_lanes() {
    let module = native_shape();
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    assert!(std::ptr::eq(reflected.module(), &module));
    let ctx = args(reflected.context_term(), "IRByteContextV1.mk");
    assert_eq!(ctx.len(), 5);
    let declarations = elements(ctx[3]);
    assert_eq!(declarations.len(), 3);
    assert_eq!(
        args(declarations[0], "IRByteFunctionV1.mk")[4],
        &boolean(true)
    );
    assert_eq!(args(declarations[1], "IRByteFunctionV1.mk")[3], &nat(1));
    let mut seen = Vec::new();
    let mut direct_arities = Vec::new();
    let mut indirect_arities = Vec::new();
    for node in nodes(reflected.context_term()) {
        let node = args(node, "IRNode.mk");
        let head = node[0].get_app_fn();
        if !seen.contains(head) {
            seen.push(head.clone());
        }
        if *head == c("IRInst.call") {
            direct_arities.push(elements(node[1]).len());
        }
        if *head == c("IRInst.callindirect") {
            indirect_arities.push(elements(node[1]).len());
            assert_eq!(args(node[0], "IRInst.callindirect")[3], &nat(1));
        }
    }
    // NullPtr shares the exact typed-constant constructor with Const.
    assert_eq!(seen.len(), 13);
    for name in [
        "const_",
        "icmp",
        "br",
        "condbr",
        "call",
        "callindirect",
        "ret",
        "extractfield",
        "load",
        "store",
        "alloca",
        "gep",
        "select",
    ] {
        assert!(
            seen.contains(&c(&format!("IRInst.{name}"))),
            "missing operation {name}"
        );
    }
    assert_eq!(direct_arities, [5, 1]);
    assert_eq!(indirect_arities, [5]);
    let sites = elements(ctx[4]);
    assert_eq!(sites.len(), nodes(reflected.context_term()).len());
    assert!(
        sites
            .iter()
            .any(|site| elements(site_fields(site)[5]).len() == 5)
    );
}

/// A reflected site's fields under either constructor: `mk`, or `mkt`, which
/// appends the operand catalog to the same six leading fields.
fn site_fields(site: &Expr) -> Vec<&Expr> {
    if *site.get_app_fn() == c("IRByteSiteV1.mkt") {
        args(site, "IRByteSiteV1.mkt")
    } else {
        args(site, "IRByteSiteV1.mk")
    }
}

/// Clean's ByteV1 ExtractField (Clean `ee4dff170`) takes the aggregate's
/// nominal type from the site's operand catalog and halts `unmodelled` at a
/// site without one. Every ExtractField site therefore carries the catalog:
/// exactly its actual aggregate operand, typed by the value's actual SSA type
/// (here a call result, so the type comes from the callee's signature), and
/// no other site changes constructor. The kernel-side consequence is replayed
/// in `tests/core_execution_byte_replay/rust_layout.rs`.
#[test]
fn only_extract_field_sites_carry_the_actual_operand_catalog() {
    let module = native_shape();
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let ctx = args(reflected.context_term(), "IRByteContextV1.mk");
    let sites = elements(ctx[4]);
    let instructions: Vec<_> = nodes(reflected.context_term())
        .into_iter()
        .map(|node| args(node, "IRNode.mk")[0])
        .collect();
    assert_eq!(sites.len(), instructions.len());
    let mut catalogued = Vec::new();
    for (site, instruction) in sites.iter().zip(&instructions) {
        if *instruction.get_app_fn() == c("IRInst.extractfield") {
            let fields = args(site, "IRByteSiteV1.mkt");
            assert_eq!(fields.len(), 7);
            let extract = args(instruction, "IRInst.extractfield");
            let rows = elements(fields[6]);
            assert_eq!(rows.len(), 1, "exactly the aggregate operand");
            let row = args(rows[0], "IRByteOperandV1.mk");
            assert_eq!(row.len(), 2);
            assert_eq!(row[0], extract[1], "the actual aggregate operand ID");
            assert_eq!(
                *row[1],
                app("IRTy.struct_", [nat(0)]),
                "the aggregate's actual SSA type, not the extracted lane's"
            );
            assert_eq!(elements(fields[5]), vec![extract[0]]);
            catalogued.push(extract[2].clone());
        } else {
            assert_eq!(args(site, "IRByteSiteV1.mk").len(), 6);
        }
    }
    assert_eq!(catalogued, [nat(0), nat(1)]);
}

#[test]
fn exact_array_struct_and_function_capture_data_are_preserved() {
    let module = native_shape();
    let term = context(&module);
    let ctx = args(&term, "IRByteContextV1.mk");
    let layouts = elements(ctx[1]);
    let structure = layouts
        .iter()
        .map(|layout| args(layout, "IRByteLayoutV1.mk"))
        .find(|row| row[0] == &app("IRTy.struct_", [nat(0)]))
        .unwrap();
    assert_eq!(structure.len(), 5);
    assert_eq!(structure[1], &nat(16));
    assert_eq!(structure[2], &nat(8));
    assert_eq!(elements(structure[4]), [&nat(0), &nat(8)]);
    let array = layouts
        .iter()
        .map(|layout| args(layout, "IRByteLayoutV1.mk"))
        .find(|row| *row[0].get_app_fn() == c("IRTy.array_"))
        .unwrap();
    assert_eq!(array[1], &nat(32));
    assert_eq!(array[2], &nat(1));
    let instructions: Vec<_> = nodes(&term)
        .iter()
        .map(|node| args(node, "IRNode.mk")[0])
        .collect();
    assert!(instructions.contains(&&app("IRInst.const_", [c("IRTy.ptr_"), c("IRConst.null_")])));
    assert!(instructions.contains(&&app(
        "IRInst.const_",
        [app("IRTy.func_", [nat(1)]), app("IRConst.func_", [nat(1)])]
    )));
    assert!(instructions.contains(&&app(
        "IRInst.const_",
        [
            app("IRTy.int_", [nat(64)]),
            app("IRConst.int_", [nat(u64::MAX)])
        ]
    )));
    assert!(instructions.contains(&&app(
        "IRInst.const_",
        [
            app("IRTy.uint_", [nat(128)]),
            app("IRConst.int_", [Expr::nat_lit_u128(u128::MAX)])
        ]
    )));
    assert!(
        instructions
            .iter()
            .any(|i| *i.get_app_fn() == c("IRInst.gep")
                && args(i, "IRInst.gep")[3] == &boolean(true))
    );
    assert!(
        instructions
            .iter()
            .any(|i| *i.get_app_fn() == c("IRInst.load")
                && args(i, "IRInst.load")[0] == &app("IRTy.func_", [nat(1)]))
    );
}

#[test]
fn layout_addresses_alignment_and_instruction_drift_change_the_context() {
    let module = native_shape();
    let original = context(&module);
    let mut shifted = module.clone();
    shifted.structs[0].fields[0].offset = Some(8);
    shifted.structs[0].fields[1].offset = Some(0);
    assert_ne!(
        original,
        context(&shifted),
        "field offsets are semantic data"
    );
    let mut locations = addresses(&module);
    locations[0].1 += 8;
    assert_ne!(
        &original,
        reflect_core_module_v1(&module, &locations)
            .unwrap()
            .context_term()
    );
    let mut changed = module.clone();
    let node = changed
        .functions
        .iter_mut()
        .flat_map(|f| &mut f.blocks)
        .flat_map(|b| &mut b.body)
        .find(|n| matches!(n.inst, Inst::Store { align: Some(8), .. }))
        .unwrap();
    if let Inst::Store { align, .. } = &mut node.inst {
        *align = Some(1);
    }
    assert_ne!(
        original,
        context(&changed),
        "site alignment must not disappear"
    );
    let mut changed = module.clone();
    let node = changed
        .functions
        .iter_mut()
        .flat_map(|f| &mut f.blocks)
        .flat_map(|b| &mut b.body)
        .find(|n| matches!(n.inst, Inst::Select { .. }))
        .unwrap();
    if let Inst::Select {
        then_val, else_val, ..
    } = &mut node.inst
    {
        std::mem::swap(then_val, else_val);
    }
    assert_ne!(
        original,
        context(&changed),
        "operand order must not disappear"
    );
}

#[test]
fn address_assignment_is_total_injective_and_has_no_extra_names() {
    let module = native_shape();
    let valid = addresses(&module);
    for bad in [
        valid[..2].to_vec(),
        vec![(valid[0].0, 0), valid[1], valid[2]],
        vec![valid[0], valid[0], valid[2]],
        vec![valid[0], (valid[1].0, valid[0].1), valid[2]],
        vec![valid[0], valid[1], (FuncId(999), 8192)],
    ] {
        assert!(reflect_core_module_v1(&module, &bad).is_err());
    }
    // Output borrows the module, not the temporary address assignment.
    let retained = {
        let temporary = addresses(&module);
        reflect_core_module_v1(&module, &temporary).unwrap()
    };
    assert_eq!(retained.context_term(), &context(&module));
}

#[test]
fn unsupported_unused_types_annotations_targets_and_signatures_are_rejected() {
    let baseline = native_shape();
    for mutate in [
        |m: &mut Module| m.types.push(Ty::F64),
        |m: &mut Module| m.target_info = None,
        |m: &mut Module| m.target_info.as_mut().unwrap().endianness = Endianness::Big,
        |m: &mut Module| m.func_types[0].is_vararg = true,
        |m: &mut Module| m.structs[0].repr = StructRepr::Packed(1),
        |m: &mut Module| m.structs[0].fields[0].offset = None,
        |m: &mut Module| m.functions[1].attrs.readnone = true,
        |m: &mut Module| {
            m.functions[1].blocks[0].body[0]
                .proofs
                .push(trust_ir::ProofAnnotation::InBounds)
        },
    ] {
        let mut changed = baseline.clone();
        mutate(&mut changed);
        assert!(reflect_core_module_v1(&changed, &addresses(&changed)).is_err());
    }
}

#[test]
fn volatile_memory_and_erased_assumptions_are_rejected_in_real_modules() {
    let baseline = native_shape();
    let mut changed = baseline.clone();
    for node in changed
        .functions
        .iter_mut()
        .flat_map(|f| &mut f.blocks)
        .flat_map(|b| &mut b.body)
    {
        if let Inst::Load { volatile, .. } = &mut node.inst {
            *volatile = true;
            break;
        }
    }
    assert!(
        reflect_core_module_v1(&changed, &addresses(&changed))
            .unwrap_err()
            .to_string()
            .contains("volatile")
    );
    let mut changed = baseline;
    let function = &mut changed.functions[2];
    let block = &mut function.blocks[0];
    let condition = block
        .body
        .iter()
        .find_map(|n| matches!(n.inst, Inst::ICmp { .. }).then(|| n.results[0]))
        .unwrap();
    block.body.insert(
        block.body.len() - 1,
        trust_ir::InstrNode::new(Inst::Assume { cond: condition }),
    );
    assert!(
        reflect_core_module_v1(&changed, &addresses(&changed))
            .unwrap_err()
            .to_string()
            .contains("Assume")
    );
}

#[test]
fn sparse_function_ids_and_reordered_blocks_do_not_become_table_positions() {
    let mut module = native_shape();
    let renamed = |id: FuncId| FuncId(17 + 23 * id.0);
    for function in &mut module.functions {
        function.id = renamed(function.id);
        function.blocks.reverse();
        for node in function.blocks.iter_mut().flat_map(|b| &mut b.body) {
            match &mut node.inst {
                Inst::Call { callee, .. } => *callee = renamed(*callee),
                Inst::Const {
                    value: Constant::FnDef(callee),
                    ..
                } => *callee = renamed(*callee),
                _ => {}
            }
        }
    }
    assert!(crate::validate_module(&module).is_empty());
    let term = context(&module);
    let ctx = args(&term, "IRByteContextV1.mk");
    let program = args(ctx[0], "IRModule.mk");
    let functions = elements(program[0]);
    assert_eq!(args(functions[0], "IRFunc.mk")[0], &nat(17));
    assert_eq!(args(functions[1], "IRFunc.mk")[0], &nat(40));
    assert_eq!(args(functions[2], "IRFunc.mk")[0], &nat(63));
    let instructions: Vec<_> = nodes(&term)
        .iter()
        .map(|node| args(node, "IRNode.mk")[0])
        .collect();
    assert!(
        instructions
            .iter()
            .any(|i| *i.get_app_fn() == c("IRInst.call") && args(i, "IRInst.call")[0] == &nat(40))
    );
    assert!(instructions.contains(&&app(
        "IRInst.const_",
        [app("IRTy.func_", [nat(1)]), app("IRConst.func_", [nat(40)])]
    )));
}

#[test]
fn equivalent_array_spellings_have_one_nonconflicting_layout_row() {
    let mut module = native_shape();
    let alias = trust_ir::TyId(module.types.len() as u32);
    module.types.push(Ty::U8);
    module.types.push(Ty::Array(alias, 32));
    let term = context(&module);
    let ctx = args(&term, "IRByteContextV1.mk");
    let arrays = elements(ctx[1])
        .into_iter()
        .filter(|layout| *args(layout, "IRByteLayoutV1.mk")[0].get_app_fn() == c("IRTy.array_"))
        .count();
    assert_eq!(arrays, 1, "catalog must not rely on first duplicate wins");
}

#[test]
fn unsupported_array_values_and_aggregate_memory_decline_instead_of_executing() {
    let mut module = native_shape();
    module.func_types.push(trust_ir::FuncTy {
        params: vec![Ty::Array(trust_ir::TyId(0), 32)],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    assert!(
        reflect_core_module_v1(&module, &addresses(&module))
            .unwrap_err()
            .to_string()
            .contains("SSA value")
    );
    let mut builder = ModuleBuilder::new_with_target_info("aggregate_memory", target());
    let byte = builder.add_type(Ty::U8);
    let sig = builder.add_func_type(vec![Ty::Ptr], vec![]);
    let mut b = builder.function("unsupported_load", sig);
    let entry = b.create_block();
    let ptr = b.add_block_param(entry, Ty::Ptr);
    b.switch_to_block(entry);
    let _value = b.load(Ty::Array(byte, 2), ptr);
    b.ret(vec![]);
    b.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    assert!(reflect_core_module_v1(&module, &addresses(&module)).is_err());
}

#[test]
fn typed_abi_signatures_are_never_erased_by_byte_reflection() {
    use trust_ir::signature_abi::{AbiArgument, AbiFrontend, AbiPassMode, AbiTarget, SignatureAbi};
    use trust_ir::{FuncTy, FuncTyId};

    let mut builder = ModuleBuilder::new_with_target_info("typed_byte_boundary", target());
    let signature = builder.add_func_type(vec![], vec![]);
    let mut body = builder.function("empty", signature);
    let entry = body.create_block();
    body.switch_to_block(entry);
    body.ret(vec![]);
    body.build();
    let baseline = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&baseline).is_empty());
    assert!(reflect_core_module_v1(&baseline, &addresses(&baseline)).is_ok());

    let abi = SignatureAbi {
        target: AbiTarget {
            triple: "aarch64-apple-darwin".into(),
            data_layout: "e-p:64:64".into(),
            abi: "aapcs64".into(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: format!("sha256:{}", "0".repeat(64)),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "reflection-test".into(),
            revision: "fixture".into(),
        },
        convention: "C".into(),
        lowered_convention: CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 0,
        arguments: vec![],
        result: AbiArgument {
            size: 0,
            align: 1,
            mode: AbiPassMode::Ignore,
            bindings: vec![],
        },
    };

    for placement in ["definition", "unused", "function-pointer-only"] {
        let mut module = baseline.clone();
        if placement == "definition" {
            module.func_types[0].abi = Some(abi.clone());
        } else {
            let id = FuncTyId(module.func_types.len() as u32);
            module.func_types.push(FuncTy {
                params: vec![],
                returns: vec![],
                abi: Some(abi.clone()),
                is_vararg: false,
            });
            if placement == "function-pointer-only" {
                module.types.push(Ty::Func(id));
            }
        }
        let errors = crate::validate_module(&module);
        assert!(
            errors.is_empty(),
            "{placement}: fixture must be valid: {errors:?}"
        );
        let error = reflect_core_module_v1(&module, &addresses(&module)).unwrap_err();
        assert!(
            error.to_string().contains("typed signature ABI transport"),
            "{placement}: {error}"
        );
    }
}

#[test]
fn borrowed_lookup_keeps_exact_module_nodes_without_changing_context() {
    let module = native_shape();
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let original = reflected.context_term().clone();
    assert_eq!(reflected.functions.len(), module.functions.len());
    assert_eq!(
        reflected.blocks.len(),
        module
            .functions
            .iter()
            .map(|f| f.blocks.len())
            .sum::<usize>()
    );
    for function in &module.functions {
        assert!(std::ptr::eq(
            reflected.function(function.id).unwrap(),
            function
        ));
        for block in &function.blocks {
            assert!(std::ptr::eq(
                reflected.block(function.id, block.id).unwrap(),
                block
            ));
            for (pc, node) in block.body.iter().enumerate() {
                assert!(std::ptr::eq(
                    reflected.node(function.id, block.id, pc).unwrap(),
                    node
                ));
            }
            assert!(
                reflected
                    .node(function.id, block.id, block.body.len())
                    .is_none()
            );
            assert!(reflected.node(function.id, block.id, usize::MAX).is_none());
        }
        if function.is_declaration() {
            assert!(reflected.block(function.id, function.entry).is_none());
            assert!(reflected.node(function.id, function.entry, 0).is_none());
        }
    }
    assert!(reflected.function(FuncId::new(u32::MAX)).is_none());
    assert!(
        reflected
            .block(FuncId::new(u32::MAX), BlockId::new(0))
            .is_none()
    );
    assert!(
        reflected
            .node(FuncId::new(u32::MAX), BlockId::new(0), 0)
            .is_none()
    );
    assert!(
        reflected
            .block(module.functions[2].id, BlockId::new(u32::MAX))
            .is_none()
    );
    assert_eq!(reflected.context_term(), &original);
    // Equal-shaped modules still return references into their own immutable
    // inputs, never a process cache indexed only by nominal IDs.
    let other_module = module.clone();
    let other = reflect_core_module_v1(&other_module, &addresses(&other_module)).unwrap();
    assert_eq!(other.context_term(), reflected.context_term());
    assert!(!std::ptr::eq(
        other.function(module.functions[2].id).unwrap(),
        reflected.function(module.functions[2].id).unwrap()
    ));
}

#[test]
fn borrowed_lookup_supports_max_sparse_ids_reordering_and_local_block_names() {
    let mut module = native_shape();
    let function_id = |id: FuncId| FuncId::new(u32::MAX - 17 * id.index());
    let block_id = |id: BlockId| BlockId::new(u32::MAX - 13 * id.index());
    for function in &mut module.functions {
        function.id = function_id(function.id);
        function.entry = block_id(function.entry);
        for block in &mut function.blocks {
            block.id = block_id(block.id);
            for node in &mut block.body {
                match &mut node.inst {
                    Inst::Call { callee, .. }
                    | Inst::Const {
                        value: Constant::FnDef(callee),
                        ..
                    } => *callee = function_id(*callee),
                    Inst::Br { target, .. } => *target = block_id(*target),
                    Inst::CondBr {
                        then_target,
                        else_target,
                        ..
                    } => {
                        *then_target = block_id(*then_target);
                        *else_target = block_id(*else_target);
                    }
                    _ => {}
                }
            }
        }
        function.blocks.reverse();
    }
    module.functions.reverse();
    assert!(crate::validate_module(&module).is_empty());
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    for function in &module.functions {
        assert!(std::ptr::eq(
            reflected.function(function.id).unwrap(),
            function
        ));
        for block in &function.blocks {
            assert!(std::ptr::eq(
                reflected.block(function.id, block.id).unwrap(),
                block
            ));
            for (pc, node) in block.body.iter().enumerate() {
                assert!(std::ptr::eq(
                    reflected.node(function.id, block.id, pc).unwrap(),
                    node
                ));
            }
        }
    }
    // Both defined functions have this SAME block ID; its function is part of
    // the key. No dense-ID allocation or cross-function fallback is permitted.
    let leaf = reflected
        .block(function_id(FuncId::new(1)), BlockId::new(u32::MAX))
        .unwrap();
    let entry = reflected
        .block(function_id(FuncId::new(2)), BlockId::new(u32::MAX))
        .unwrap();
    assert!(!std::ptr::eq(leaf, entry));
    assert_ne!(leaf.body.len(), entry.body.len());
    assert!(reflected.function(FuncId::new(0)).is_none());
    assert!(
        reflected
            .block(function_id(FuncId::new(2)), BlockId::new(0))
            .is_none()
    );
}

#[test]
fn borrowed_index_construction_retains_duplicate_and_size_refusal() {
    let mut duplicate_function = native_shape();
    duplicate_function
        .functions
        .push(duplicate_function.functions[1].clone());
    assert!(reflect_core_module_v1(&duplicate_function, &addresses(&duplicate_function)).is_err());
    let mut duplicate_block = native_shape();
    let function = &mut duplicate_block.functions[2];
    function.blocks.push(function.blocks[0].clone());
    assert!(reflect_core_module_v1(&duplicate_block, &addresses(&duplicate_block)).is_err());

    let mut oversized = native_shape();
    let import = oversized.functions[0].clone();
    oversized.functions = vec![import; 65_537];
    assert!(
        reflect_core_module_v1(&oversized, &[])
            .unwrap_err()
            .to_string()
            .contains("table limit")
    );
    let mut oversized = native_shape();
    oversized.functions[2].blocks = vec![Block::new(BlockId::new(0)); 65_537];
    assert!(
        reflect_core_module_v1(&oversized, &addresses(&oversized))
            .unwrap_err()
            .to_string()
            .contains("block limit")
    );
}
