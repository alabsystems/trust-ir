// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) const ZERO: &str = "lane count must be nonzero";
pub(super) const NESTED: &str = "nested vector lanes are not supported";
pub(super) const LANE: &str = "lane type must be bool, integer, or float";
pub(super) fn bad() -> Ty {
    Ty::Vector(Box::new(Ty::Ptr), 0)
}
pub(super) fn block_error(block: u32, ty: &str, reason: &str) -> ValidationError {
    ValidationError::InvalidVectorType {
        block,
        ty: ty.into(),
        reason: reason.into(),
    }
}
pub(super) fn module_error(location: &str, reason: &str) -> ValidationError {
    ValidationError::InvalidModuleVectorType {
        location: location.into(),
        ty: "<0 x ptr>".into(),
        reason: reason.into(),
    }
}
pub(super) fn global(name: &str, ty: Ty) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable: false,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: Some(3),
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}
pub(super) fn field(name: &str) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty: bad(),
        offset: None,
    }
}
pub(super) fn fixture() -> Module {
    let mut module = Module::new("vectors");
    module.types.push(bad());
    module.func_types.push(FuncTy {
        params: vec![bad()],
        returns: vec![bad()],
        abi: None,
        is_vararg: false,
    });
    module.globals.push(global("G", bad()));
    module.drop_glue.push(DropGlueEntry {
        glue: FuncId::new(1),
        ty: bad(),
    });
    module.structs.push(StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![field("sf")],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![field("rf")],
    });
    module.enums.push(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![bad()],
            field_names: vec![],
        }],
    ));
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![bad()],
    });
    module
}
