// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use trust_ir::dialect::vector as vec;
#[test]
fn every_real_vector_family_matches_whole_ordinary_typed_success() {
    let m = fixture();
    for op in [
        vec::pack_lanes(vec_ty(Ty::I32, 4), [v(0); 4]),
        vec::extract_lane(vec_ty(Ty::I32, 4), v(4), 2),
        vec::insert_lane(vec_ty(Ty::I32, 4), v(4), 2, v(0)),
        vec::mask_to_bits(vec_ty(Ty::Bool, 4), v(11), Ty::I32),
        vec::reduce(vec_ty(Ty::I32, 4), v(4), vec::ReduceKind::Add),
        vec::shuffle(vec_ty(Ty::I32, 4), v(4), vec![3, 2, 1, 0]),
        vec::fma(vec_ty(Ty::F32, 4), v(9), v(9), v(9)),
    ] {
        assert!(run(&m, &node(op, 1), None).0.is_empty());
    }
    for (elem, lanes) in [
        (Ty::I8, 16),
        (Ty::I16, 8),
        (Ty::I32, 4),
        (Ty::I64, 2),
        (Ty::I8, 8),
        (Ty::F32, 4),
        (Ty::F64, 2),
    ] {
        let mut m = fixture();
        m.functions[0].blocks[0].params[0].1 = elem.clone();
        let op = vec::pack_lanes(vec_ty(elem, lanes), vec![v(0); lanes as usize]);
        assert!(run(&m, &node(op, 1), None).0.is_empty());
    }
    for lanes in [2, 4, 8, 16] {
        let mut m = fixture();
        m.functions[0].blocks[0].params[11].1 = vec_ty(Ty::Bool, lanes);
        let op = vec::mask_to_bits(
            vec_ty(Ty::Bool, lanes),
            v(11),
            if lanes == 2 { Ty::I64 } else { Ty::I32 },
        );
        assert!(run(&m, &node(op, 1), None).0.is_empty());
    }
}
#[test]
fn all_real_vector_families_preserve_full_malformed_type_and_payload_diagnostics() {
    let m = fixture();
    for mut op in [
        vec::pack_lanes(vec_ty(Ty::I32, 4), [v(0); 4]),
        vec::extract_lane(vec_ty(Ty::I32, 4), v(4), 2),
        vec::insert_lane(vec_ty(Ty::I32, 4), v(4), 2, v(0)),
        vec::mask_to_bits(vec_ty(Ty::Bool, 4), v(11), Ty::I32),
        vec::reduce(vec_ty(Ty::I32, 4), v(4), vec::ReduceKind::Add),
        vec::shuffle(vec_ty(Ty::I32, 4), v(4), vec![3, 2, 1, 0]),
        vec::fma(vec_ty(Ty::F32, 4), v(9), v(9), v(9)),
    ] {
        op.result_tys = vec![Ty::Tuple(vec![
            Ty::handle("bad\n'é", "rt::中"),
            Ty::Ref(Box::new(Ty::Bool)),
        ])];
        op.attrs.clear();
        assert!(matches!(
            &run(&m, &node(op, 1), None).0[..],
            [ValidationError::InvalidVectorDialectOp { .. }]
        ));
    }
}
#[test]
fn any_unresolved_vector_operand_discards_whole_typed_validation_but_not_payload_checks() {
    let m = fixture();
    let mut op = vec::pack_lanes(vec_ty(Ty::I32, 4), [v(1), v(999), v(1), v(1)]);
    assert!(run(&m, &node(op.clone(), 1), None).0.is_empty());
    op.operands[1] = v(0);
    assert!(
        matches!(&run(&m,&node(op.clone(),1),None).0[..],[ValidationError::InvalidVectorDialectOp{reason,..}]if reason.contains("lane operand 0"))
    );
    op.operands[1] = v(999);
    op.version = 2;
    assert!(
        matches!(&run(&m,&node(op,1),None).0[..],[ValidationError::InvalidVectorDialectOp{reason,..}]if reason.contains("version 2"))
    );
}
#[test]
fn unknown_vector_op_is_before_version_error_after_actual_operand_prefix_collection() {
    let m = fixture();
    let op = DialectInst::new("vector", "unknown中")
        .with_version(99)
        .with_operands([v(0), v(1)]);
    assert!(
        matches!(&run(&m,&node(op,0),None).0[..],[ValidationError::InvalidVectorDialectOp{reason,..}]if reason.starts_with("unknown vector op")&&reason.contains("expected one of"))
    );
}
#[test]
fn vector_first_attribute_shapes_indices_reduction_and_bit_order_keep_original_order() {
    let m = fixture();
    for op in [
        vec::extract_lane(vec_ty(Ty::I32, 4), v(4), u32::MAX),
        vec::insert_lane(vec_ty(Ty::I32, 4), v(4), 2, v(0))
            .with_attr("lane", AttrValue::U64(u64::MAX)),
        vec::shuffle(vec_ty(Ty::I32, 4), v(4), vec![0, 1, 2, 4]),
        vec::reduce(vec_ty(Ty::I32, 4), v(4), vec::ReduceKind::Or)
            .with_attr("kind", AttrValue::Str("bad".into())),
        vec::mask_to_bits(vec_ty(Ty::Bool, 4), v(11), Ty::I64),
    ] {
        let _ = run(&m, &node(op, 1), None);
    }
    let mut op = vec::mask_to_bits(vec_ty(Ty::Bool, 4), v(11), Ty::I32);
    op.attrs.retain(|a| a.name != "bit_order");
    op = op.with_attr("bit_order", AttrValue::Str("wrong中".into()));
    assert!(
        matches!(&run(&m,&node(op,1),None).0[..],[ValidationError::InvalidVectorDialectOp{reason,..}]if reason.contains("unsupported bit_order"))
    );
    let mut overflow = vec::insert_lane(vec_ty(Ty::I32, 4), v(4), 0, v(0));
    overflow
        .attrs
        .iter_mut()
        .find(|a| a.name == "lane")
        .unwrap()
        .value = AttrValue::U64(u64::MAX);
    assert!(
        matches!(&run(&m,&node(overflow,1),None).0[..],[ValidationError::InvalidVectorDialectOp{reason,..}]if reason.contains("does not fit in u32"))
    );
    let mut reduce = vec::reduce(vec_ty(Ty::I32, 4), v(4), vec::ReduceKind::Add);
    reduce
        .attrs
        .iter_mut()
        .find(|a| a.name == "kind")
        .unwrap()
        .value = AttrValue::Str("bad".into());
    assert!(
        matches!(&run(&m,&node(reduce,1),None).0[..],[ValidationError::InvalidVectorDialectOp{reason,..}]if reason.contains("unsupported reduce kind"))
    );
}
