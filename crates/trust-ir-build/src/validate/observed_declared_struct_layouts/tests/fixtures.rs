// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn field(name: &str, ty: Ty, offset: Option<u64>) -> trust_ir::ty::FieldDef {
    trust_ir::ty::FieldDef {
        name: name.into(),
        ty,
        offset,
    }
}
pub(super) fn strukt(
    id: u32,
    size: Option<u64>,
    align: Option<u64>,
    fields: Vec<trust_ir::ty::FieldDef>,
) -> trust_ir::ty::StructDef {
    trust_ir::ty::StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        fields,
        size,
        align,
        repr: trust_ir::StructRepr::Rust,
        origin: None,
    }
}
pub(super) fn valid() -> Module {
    let mut m = Module::new("declared-layout");
    m.structs = vec![
        strukt(
            0,
            Some(16),
            Some(8),
            vec![
                field("large", Ty::U64, Some(0)),
                field("small", Ty::U8, Some(8)),
                field("trailing", Ty::Unit, Some(16)),
            ],
        ),
        strukt(1, Some(0), Some(1), vec![field("unit", Ty::Unit, Some(0))]),
    ];
    m
}
pub(super) fn invalid() -> Module {
    let mut m = valid();
    m.structs[0].fields[1].offset = Some(1);
    m.structs[1].align = Some(0);
    m
}
pub(super) fn target(triple: String) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple,
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}
