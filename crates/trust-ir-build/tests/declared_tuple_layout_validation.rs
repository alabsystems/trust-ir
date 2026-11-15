use trust_ir::{Endianness, Module, TargetInfo, TupleLayoutDescriptor, Ty, TyId};
use trust_ir_build::validate::{ValidationError, validate_module};

fn module() -> Module {
    let mut m = Module::new("tuple_layout_validation");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let tuple_type = m
        .add_type(Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]))
        .expect("Module::add_type: test fixture");
    m.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type,
        size: 16,
        align: 8,
        field_offsets: vec![8, 0, 9],
    });
    m
}

#[test]
fn tuple_layout_validator_checks_unused_rows() {
    let valid = module();
    assert!(validate_module(&valid).is_empty());
    let mut bad = valid.clone();
    bad.tuple_layouts[0].field_offsets[0] = 0;
    assert!(
        validate_module(&bad)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { .. }))
    );
    let mut bad = valid.clone();
    bad.tuple_layouts[0].tuple_type = TyId::new(100);
    assert!(
        validate_module(&bad)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { .. }))
    );
    let mut bad = valid;
    bad.target_info = None;
    assert!(
        validate_module(&bad)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { .. }))
    );
}
