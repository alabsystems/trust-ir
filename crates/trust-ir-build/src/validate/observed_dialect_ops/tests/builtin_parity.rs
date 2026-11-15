// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn gpu_all_thirteen_payloads_keep_original_opaque_version_operand_result_and_attribute_rules() {
    let m = fixture();
    for name in [
        "thread_id_x",
        "thread_id_y",
        "thread_id_z",
        "block_id_x",
        "block_id_y",
        "block_id_z",
        "block_dim_x",
        "block_dim_y",
        "block_dim_z",
        "grid_dim_x",
        "grid_dim_y",
        "grid_dim_z",
        "barrier",
    ] {
        let op = DialectInst::new("gpu", name)
            .with_version(999)
            .with_operand(v(999))
            .with_result_ty(Ty::handle("bad", "rt"))
            .with_attr("bad.name", AttrValue::Bytes(vec![0; 20]));
        assert!(run(&m, &node(op, 7), None).0.is_empty());
    }
    assert_eq!(
        run(&m, &node(DialectInst::new("gpu", "bad\n"), 0), None)
            .0
            .len(),
        1
    );
}
#[test]
fn avx512_all_families_preserve_first_attr_truncation_and_unknownop_failures() {
    let m = fixture();
    for op in [
        DialectInst::new("avx512", "mask_cmp")
            .with_operands([v(0), v(1)])
            .with_attr("predicate", AttrValue::Str("ult".into())),
        DialectInst::new("avx512", "vpternlog")
            .with_operands([v(0), v(0), v(0)])
            .with_attr("imm8", AttrValue::U64(u64::MAX)),
        DialectInst::new("avx512", "compress").with_operands([v(0), v(0)]),
        DialectInst::new("avx512", "expand").with_operands([v(0), v(0)]),
    ] {
        let op = op
            .with_result_ty(Ty::handle("opaque", "rt"))
            .with_version(99);
        assert!(run(&m, &node(op.clone(), 1), None).0.is_empty());
        let mut bad = op;
        bad.operands.clear();
        assert!(
            matches!(&run(&m,&node(bad,1),None).0[..],[ValidationError::InvalidVectorDialectOp{reason,..}]if reason.starts_with("unknown op"))
        );
    }
}
#[test]
fn ane_default_and_illtyped_optional_attributes_are_not_new_validation_restrictions() {
    let m = fixture();
    for name in ["tensor_conv", "tensor_matmul"] {
        let op = DialectInst::new("ane", name)
            .with_operands([v(0), v(0)])
            .with_result_ty(Ty::Bool)
            .with_attr("stride", AttrValue::I64(-1))
            .with_attr("padding", AttrValue::Str("bad".into()))
            .with_version(999);
        assert!(run(&m, &node(op, 1), None).0.is_empty());
    }
    let op = DialectInst::new("ane", "dma_transfer")
        .with_operands([v(0), v(0), v(0)])
        .with_attr("direction", AttrValue::Ty(Ty::Ptr));
    assert!(run(&m, &node(op.clone(), 0), None).0.is_empty());
    assert!(matches!(
        &run(&m, &node(op.with_result_ty(Ty::Bool), 1), None).0[..],
        [ValidationError::InvalidVectorDialectOp { .. }]
    ));
}
#[test]
fn rust_tls_complete_schema_name_and_attribute_order_matches_ordinary_decoder() {
    let m = fixture();
    let good = trust_ir::dialect::trust_rust::thread_local_addr("sym中");
    assert!(run(&m, &node(good.clone(), 1), None).0.is_empty());
    for op in [
        good.clone().with_version(2),
        good.clone().with_operand(v(0)),
        good.clone().with_attr("symbol", AttrValue::Str("x".into())),
        DialectInst::new("trust_rust", "thread_local_addr")
            .with_result_ty(Ty::Tuple(vec![Ty::Bool])),
    ] {
        assert!(matches!(
            &run(&m, &node(op.clone(), 1), None).0[..],
            [ValidationError::InvalidVectorDialectOp { .. }]
        ));
    }
    let mut op = good.clone();
    op.attrs[0].name = "bad.name".into();
    assert!(
        matches!(&run(&m,&node(op,1),None).0[..],[ValidationError::InvalidVectorDialectOp{reason,..}]if reason.starts_with("invalid dialect op name"))
    );
    let mut op = good;
    op.attrs[1].value = AttrValue::Str(String::new());
    assert!(
        matches!(&run(&m,&node(op,1),None).0[..],[ValidationError::InvalidVectorDialectOp{reason,..}]if reason.contains("symbol attribute must"))
    );
}
#[test]
fn unknown_namespace_and_dead_or_unrelated_nodes_keep_original_local_opacity() {
    let m = fixture();
    for name in ["unknown", "bad.namespace", "", "中"] {
        let n = node(DialectInst::new(name, "bad.op").with_operand(v(999)), 7);
        assert!(run(&m, &n, None).0.is_empty());
        assert!(matches!(
            &run(&m, &n, Some(&schema())).0[..],
            [ValidationError::InvalidDialectSchema { .. }]
        ));
    }
    let n = InstrNode::new(Inst::Unreachable);
    assert!(run(&m, &n, Some(&schema())).0.is_empty());
}
