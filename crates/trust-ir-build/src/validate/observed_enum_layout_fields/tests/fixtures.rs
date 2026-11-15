// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        field_names: vec![],
        fields,
    }
}
pub(super) fn descriptor(size: u64, align: u64, offsets: Vec<Vec<u64>>) -> EnumLayoutDescriptor {
    EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size,
        align,
        variant_field_offsets: offsets,
    }
}
pub(super) fn fixture() -> (Module, EnumDef, EnumLayoutDescriptor) {
    (
        Module::new("enum-fields"),
        EnumDef::new(
            EnumId::new(7),
            "Eλ",
            vec![variant("Vλ", vec![Ty::U64, Ty::U8, Ty::Unit])],
        ),
        descriptor(16, 8, vec![vec![0, 8, 16]]),
    )
}
pub(super) fn compact() -> (Module, EnumDef, EnumLayoutDescriptor) {
    (
        Module::new("compact-fields"),
        EnumDef::new(EnumId::new(7), "Eλ", vec![variant("Vλ", vec![Ty::U8])]),
        descriptor(0, 0, vec![vec![1]]),
    )
}
pub(super) fn strukt(
    id: u32,
    size: Option<u64>,
    align: Option<u64>,
    fields: Vec<FieldDef>,
) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        fields,
        size,
        align,
        repr: trust_ir::StructRepr::Rust,
        origin: None,
    }
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
