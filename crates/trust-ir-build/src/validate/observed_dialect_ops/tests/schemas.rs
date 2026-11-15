// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn frozen_schema_exact_success_and_namespace_version_operation_prefix_remain_ordered() {
    let m = fixture();
    let registry = schema();
    assert!(run(&m, &node(operation(), 1), Some(&registry)).0.is_empty());
    let mut op = operation();
    op.dialect = "absent".into();
    assert!(
        matches!(&run(&m,&node(op,1),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("UnknownDialect"))
    );
    let mut op = operation();
    op.version = 2;
    op.op = "absent".into();
    assert!(
        matches!(&run(&m,&node(op.clone(),1),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("VersionMismatch"))
    );
    op.version = 1;
    assert!(
        matches!(&run(&m,&node(op,1),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("UnknownOperation"))
    );
}
#[test]
fn every_lexical_role_precedes_registry_lookup_and_preserves_verbatim_debug_names() {
    let m = fixture();
    let registry = schema();
    for role in 0..3 {
        let mut op = operation().with_version(99);
        match role {
            0 => op.dialect = "bad.中".into(),
            1 => op.op = "".into(),
            _ => op.attrs[0].name = "bad\n'".into(),
        };
        assert!(
            matches!(&run(&m,&node(op,7),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("InvalidName(NameError")&&!reason.contains("VersionMismatch"))
        );
    }
}
#[test]
fn schema_fixed_variadic_prefix_and_result_type_count_keep_exact_first_error() {
    let m = fixture();
    let registry = schema();
    let mut op = operation();
    op.operands.clear();
    op.result_tys.clear();
    assert!(
        matches!(&run(&m,&node(op,0),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("OperandCount"))
    );
    let mut op = operation();
    op.result_tys = vec![Ty::I32];
    assert!(
        matches!(&run(&m,&node(op,0),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.ends_with("ResultTypes"))
    );
    assert!(
        matches!(&run(&m,&node(operation(),0),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("ResultCount"))
    );
    let registry = DialectSchemaRegistry::new([DialectSchema {
        namespace: "tail".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "op".into(),
            operands: vec![Ty::Bool.into(), OperandType::VariadicExact(Ty::I32)],
            results: vec![],
            attributes: vec![],
        }],
    }])
    .unwrap();
    for ids in [
        vec![],
        vec![v(16)],
        vec![v(16), v(0), v(0)],
        vec![v(16), v(1)],
    ] {
        let op = DialectInst::new("tail", "op").with_operands(ids);
        let _ = run(&m, &node(op, 0), Some(&registry));
    }
}
#[test]
fn schema_exact_actual_types_do_not_defer_refinement_or_unknown_ssa() {
    let mut m = fixture();
    let registry = schema();
    for (id, label) in [
        (1, "OperandType"),
        (999, "UndefinedOperand"),
        (13, "OperandType"),
    ] {
        let mut op = operation();
        op.operands = vec![v(id)];
        assert!(
            matches!(&run(&m,&node(op,1),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains(label))
        );
    }
    m.functions[0].blocks[0].params[0].1 = Ty::Refine(
        trust_ir::value::TyId::new(0),
        trust_ir::value::PredId::new(0),
    );
    assert!(
        matches!(&run(&m,&node(operation(),1),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("Refine(TyId(0), PredId(0))"))
    );
}
#[test]
fn schema_functions_resolve_module_table_and_keep_unavailable_wrongkind_vararg_and_full_abi() {
    let registry = callback_schema();
    let m = fixture();
    assert!(run(&m, &node(call(14), 1), Some(&registry)).0.is_empty());
    for (id, label) in [
        (17, "FunctionTypeUnavailable"),
        (12, "ExpectedFunctionOperand"),
        (999, "UndefinedOperand"),
    ] {
        assert!(
            matches!(&run(&m,&node(call(id),1),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains(label))
        );
    }
    for mode in abi_fixture::modes() {
        let mut m = fixture();
        m.func_types[1].abi = Some(abi_fixture::abi(mode));
        // Ordinary schema matching does not canonicalize or validate raw ABI.
        assert!(run(&m, &node(call(14), 1), Some(&registry)).0.is_empty());
        m.func_types[1].params = vec![Ty::I64];
        let e = run(&m, &node(call(14), 1), Some(&registry)).0;
        assert!(
            matches!(&e[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("FunctionSignature")&&reason.contains("SignatureAbi")&&reason.contains("source_abi"))
        );
    }
    let mut m = fixture();
    m.func_types[1].is_vararg = true;
    assert!(
        matches!(&run(&m,&node(call(14),1),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("is_vararg: true"))
    );
}
#[test]
fn schema_unknown_duplicate_wrong_tag_and_missing_attrs_preserve_first_cause() {
    let m = fixture();
    let registry = schema();
    let mut unknown = operation();
    unknown.attrs[0].name = "unknown".into();
    let mut duplicate = operation().with_attr("slot", AttrValue::Str("wrong".into()));
    let mut wrong = operation();
    wrong.attrs[0].value = AttrValue::I64(7);
    let mut missing = operation();
    missing.attrs.clear();
    for (op, label) in [
        (unknown, "UnknownAttribute"),
        (duplicate.clone(), "DuplicateAttribute"),
        (wrong, "AttributeType"),
        (missing, "MissingAttribute"),
    ] {
        assert!(
            matches!(&run(&m,&node(op,1),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains(label))
        );
    }
    duplicate.attrs[0].value = AttrValue::Bool(false);
    assert!(
        matches!(&run(&m,&node(duplicate,1),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("AttributeType")&&!reason.contains("DuplicateAttribute"))
    );
}
#[test]
fn schema_wide_attributes_remain_supported_and_original_order_is_frozen_data() {
    let m = fixture();
    let registry = DialectSchemaRegistry::new([DialectSchema {
        namespace: "wide".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "op".into(),
            operands: vec![],
            results: vec![],
            attributes: (0..70)
                .rev()
                .map(|i| AttributeSchema {
                    name: format!("slot{i:02}"),
                    kind: AttributeKind::U64,
                })
                .collect(),
        }],
    }])
    .unwrap();
    let mut op = DialectInst::new("wide", "op");
    for i in (0..70).rev() {
        op = op.with_attr(format!("slot{i:02}"), AttrValue::U64(i));
    }
    assert!(run(&m, &node(op.clone(), 0), Some(&registry)).0.is_empty());
    op.attrs.remove(0);
    assert!(
        matches!(&run(&m,&node(op,0),Some(&registry)).0[..],[ValidationError::InvalidDialectSchema{reason,..}]if reason.contains("MissingAttribute"))
    );
}
#[test]
fn complete_builtin_error_is_retained_before_optional_schema_error_in_original_order() {
    let m = fixture();
    let registry = schema();
    let op = DialectInst::new("vector", "bad");
    let e = run(&m, &node(op, 0), Some(&registry)).0;
    assert!(matches!(
        &e[..],
        [
            ValidationError::InvalidVectorDialectOp { .. },
            ValidationError::InvalidDialectSchema { .. }
        ]
    ));
}
