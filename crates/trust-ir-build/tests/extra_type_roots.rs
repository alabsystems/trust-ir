//! Detached roots use the canonical mapper, not a synthetic signature or a
//! second type walker. These are DATA correspondence controls, not admission.

use trust_ir::{
    ClosureTy, ClosureTyId, FieldDef, FuncTy, FuncTyId, Module, StructDef, StructId, Ty, TyId,
};
use trust_ir_build::{MergeError, MergePolicy, RetainedImage, merge_into, merge_into_with_roots};

const POLICY: MergePolicy = MergePolicy::VERIFICATION_IMAGE;

fn source() -> (Module, Vec<Ty>) {
    let mut source = Module::new("source");
    source.structs.push(StructDef {
        id: StructId::new(0),
        name: "ActualNominal".into(),
        fields: vec![FieldDef {
            name: "value".into(),
            ty: Ty::U64,
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: trust_ir::StructRepr::C,
        origin: None,
    });
    source.types.push(Ty::Struct(StructId::new(0)));
    source.func_types.push(FuncTy {
        params: vec![Ty::Bool],
        returns: vec![Ty::Unit],
        is_vararg: false,
        abi: None,
    });
    source.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::Array(TyId::new(0), 3)],
    });
    let roots = vec![
        Ty::Bool,
        Ty::Unit,
        Ty::Tuple(vec![
            Ty::Array(TyId::new(0), 3),
            Ty::Closure(ClosureTyId::new(0)),
        ]),
    ];
    (source, roots)
}

fn host() -> Module {
    let mut host = Module::new("host");
    host.types.push(Ty::U8);
    host.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: None,
    });
    host
}

#[test]
fn extra_roots_preserve_ordinary_merge_and_do_not_add_carrier_signatures() {
    let (source, roots) = source();
    let original_source = source.clone();
    let original_roots = roots.clone();
    let mut ordinary = host();
    merge_into(&mut ordinary, &source, &POLICY).unwrap();
    let mut actual = host();
    let (map, mapped) = merge_into_with_roots(&mut actual, &source, &POLICY, &roots).unwrap();
    assert_eq!(
        actual, ordinary,
        "the module is exactly the ordinary canonical merge"
    );
    assert_eq!(source, original_source);
    assert_eq!(roots, original_roots);
    assert_eq!(
        actual.func_types.len(),
        2,
        "only genuine input signature rows survive"
    );
    assert_eq!(mapped[0..2], [Ty::Bool, Ty::Unit]);
    assert_eq!(
        mapped[2],
        Ty::Tuple(vec![
            Ty::Array(map.ty(TyId::new(0)).unwrap(), 3),
            Ty::Closure(map.closure(ClosureTyId::new(0)).unwrap())
        ])
    );
    assert!(trust_ir_build::validate::validate_type_roots(&actual, &mapped).is_empty());
}

#[test]
fn detached_bool_and_unit_roots_need_no_signature_row_at_all() {
    let source = Module::new("no_signature");
    let mut host = Module::new("no_signature_host");
    let (_, mapped) =
        merge_into_with_roots(&mut host, &source, &POLICY, &[Ty::Bool, Ty::Unit]).unwrap();
    assert_eq!(mapped, [Ty::Bool, Ty::Unit]);
    assert!(host.func_types.is_empty());
}

#[test]
fn malformed_extra_roots_refuse_transactionally_without_healing_dangling_ids() {
    let (source, _) = source();
    for root in [
        Ty::Array(TyId::new(99), 1),
        Ty::Func(FuncTyId::new(99)),
        Ty::Closure(ClosureTyId::new(99)),
        Ty::Error,
        Ty::Vector(Box::new(Ty::U8), 0),
    ] {
        let mut actual = host();
        let before = actual.clone();
        assert!(matches!(
            merge_into_with_roots(&mut actual, &source, &POLICY, &[root]),
            Err(MergeError::InvalidTypeRoots { .. })
        ));
        assert_eq!(actual, before);
    }
    let empty = Module::new("empty");
    let mut actual = host();
    let before = actual.clone();
    assert!(
        merge_into_with_roots(&mut actual, &empty, &POLICY, &[Ty::Func(FuncTyId::new(0))]).is_err(),
        "a synthetic carrier must not make source signature zero appear to exist"
    );
    assert_eq!(actual, before);
}

#[test]
fn retained_extra_root_merge_preserves_actual_origin_receipts() {
    let (source, roots) = source();
    let source = RetainedImage::new(source).unwrap();
    let host = RetainedImage::new(host()).unwrap();
    let (ordinary, _) = host.merge(&source, &POLICY).unwrap();
    let (actual, _, mapped) = host.merge_with_roots(&source, &POLICY, &roots).unwrap();
    assert_eq!(actual.module(), ordinary.module());
    assert!(trust_ir_build::validate::validate_type_roots(actual.module(), &mapped).is_empty());
    // Replay the actual receipt DAG. Canonical merge may conservatively append
    // table rows on repeated input; idempotence is not its contract. Detached
    // roots must preserve exactly the ordinary replay's output and receipts.
    let (ordinary_again, _) = actual.merge(&source, &POLICY).unwrap();
    let (again, _, mapped_again) = actual.merge_with_roots(&source, &POLICY, &roots).unwrap();
    assert_eq!(again.module(), ordinary_again.module());
    assert!(
        trust_ir_build::validate::validate_type_roots(again.module(), &mapped_again).is_empty()
    );
}
