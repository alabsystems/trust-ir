// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn strukt(id: u32, fields: Vec<Ty>) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        fields: fields
            .into_iter()
            .map(|ty| FieldDef {
                name: "field".into(),
                ty,
                offset: None,
            })
            .collect(),
        size: None,
        align: None,
        repr: StructRepr::C,
        origin: None,
    }
}
pub(super) fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}
pub(super) fn cycle() -> Module {
    let mut m = Module::new("cycles");
    m.structs = vec![strukt(0, vec![s(1)]), strukt(1, vec![s(0)])];
    m
}
pub(super) fn several() -> Module {
    let mut m = cycle();
    m.structs.push(strukt(99, vec![s(99)]));
    m.structs.push(strukt(4, vec![s(4)]));
    m
}
pub(super) fn all_families() -> Module {
    let mut m = Module::new("all");
    m.structs.push(strukt(4, vec![Ty::Enum(EnumId::new(7))]));
    m.enums.push(EnumDef::new(
        EnumId::new(7),
        "E'λ\n\0",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![Ty::Record(RecordId::new(2))],
            field_names: vec![],
        }],
    ));
    m.records.push(RecordDef {
        id: RecordId::new(2),
        name: "R'尾".into(),
        fields: vec![FieldDef {
            name: "capture".into(),
            ty: Ty::Closure(ClosureTyId::new(0)),
            offset: None,
        }],
    });
    m.closure_types.push(ClosureTy {
        func: FuncTyId::new(999),
        captures: vec![Ty::Array(TyId::new(0), 0)],
    });
    m.types.push(s(4));
    m
}
pub(super) fn row_text() -> Module {
    let mut m = Module::new("row_text");
    m.types.push(Ty::Tuple(vec![
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::handle("λ🦀'\n", "rt::Name"),
    ]));
    m
}
