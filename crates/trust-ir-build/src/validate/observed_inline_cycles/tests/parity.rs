// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_scalar_and_acyclic_modules_match_complete_ordinary_empty_result() {
    assert!(run(&Module::new("")).0.is_empty());
    let mut m = Module::new("acyclic");
    m.structs = vec![strukt(0, vec![s(1)]), strukt(1, vec![Ty::U64])];
    m.types = vec![Ty::U8, Ty::Tuple(vec![Ty::I64, Ty::Bool])];
    assert!(run(&m).0.is_empty());
}
#[test]
fn all_five_identity_families_form_one_whole_original_component_and_raw_diagnostic() {
    let m = all_families();
    let errors = run(&m).0;
    assert_eq!(errors.len(), 1);
    let ValidationError::InlineAggregateCycle { ty } = &errors[0] else {
        panic!()
    };
    assert!(ty.starts_with("struct #4 'S4' (cycle through enum #7 'E'λ\n\0'"));
    for text in ["record #2 'R'尾'", "closure type #0"] {
        assert!(ty.contains(text));
    }
    assert!(ty.contains(&format!("type #0 ({})", m.types[0])));
}
#[test]
fn every_single_identity_self_edge_is_reported_without_needing_a_size_declaration() {
    let mut m = Module::new("selfs");
    m.structs.push(strukt(0, vec![s(0)]));
    m.enums.push(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![Ty::Enum(EnumId::new(0))],
            field_names: vec![],
        }],
    ));
    m.records.push(RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![FieldDef {
            name: "r".into(),
            ty: Ty::Record(RecordId::new(0)),
            offset: None,
        }],
    });
    m.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::Closure(ClosureTyId::new(0))],
    });
    m.types.push(Ty::Array(TyId::new(0), 0));
    assert_eq!(run(&m).0.len(), 5);
}
#[test]
fn disjoint_components_duplicate_edges_and_physical_table_order_preserve_complete_report_order() {
    let mut m = several();
    m.structs[0].fields.push(FieldDef {
        name: "again".into(),
        ty: s(1),
        offset: None,
    });
    m.structs.swap(0, 3);
    let errors = run(&m).0;
    assert_eq!(errors.len(), 3);
    for (error, id) in errors.iter().zip([0, 4, 99]) {
        assert!(
            matches!(error,ValidationError::InlineAggregateCycle{ty}if ty.starts_with(&format!("struct #{id} ")))
        );
    }
}
#[test]
fn actual_indexed_definition_preference_and_first_scan_fallback_are_distinct_from_layout_lookup() {
    let mut m = Module::new("duplicates");
    m.structs.push(strukt(7, vec![Ty::U8]));
    for id in 1..7 {
        m.structs.push(strukt(id, vec![Ty::U8]));
    }
    m.structs.push(strukt(7, vec![s(7)]));
    assert_eq!(run(&m).0.len(), 1);
    m.structs[7].fields.clear();
    m.structs[0].fields = vec![FieldDef {
        name: "self".into(),
        ty: s(7),
        offset: None,
    }];
    assert!(run(&m).0.is_empty());
    m.structs.pop();
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn inline_zero_array_vector_tuple_and_refinement_routes_retain_original_cycle_edges() {
    for ty in [
        Ty::Array(TyId::new(0), 0),
        Ty::Refine(TyId::new(0), PredId::new(7)),
        Ty::Vector(Box::new(s(0)), 0),
        Ty::Tuple(vec![Ty::U8, s(0)]),
    ] {
        let mut m = Module::new("inline");
        m.types.push(s(0));
        m.structs.push(strukt(0, vec![ty]));
        assert_eq!(run(&m).0.len(), 1);
    }
}
#[test]
fn every_indirection_stops_at_its_original_boundary_without_following_the_pointee() {
    for ty in [
        Ty::Ptr,
        Ty::FatPtr(trust_ir::ty::FatPtrKind::Str),
        Ty::Ref(Box::new(s(0))),
        Ty::RefMut(Box::new(s(0))),
        Ty::PtrConst(Box::new(s(0))),
        Ty::PtrMut(Box::new(s(0))),
        Ty::Rc(Box::new(s(0))),
        Ty::Func(FuncTyId::new(0)),
        Ty::Sequence(TyId::new(0)),
        Ty::Set(TyId::new(0), trust_ir::ty::SetRepr::Boxed),
        Ty::handle("H", "runtime"),
        Ty::Dialect(Box::new(trust_ir::DialectTy::new("ns", "D", 1))),
    ] {
        let mut m = Module::new("handles");
        m.types.push(s(0));
        m.structs.push(strukt(0, vec![ty]));
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn missing_nominal_closure_and_type_row_ids_add_no_edges_or_cycle_diagnostics() {
    let mut m = Module::new("missing");
    m.structs.push(strukt(
        0,
        vec![
            s(999),
            Ty::Enum(EnumId::new(999)),
            Ty::Record(RecordId::new(999)),
            Ty::Closure(ClosureTyId::new(999)),
            Ty::Array(TyId::new(999), 0),
            Ty::Refine(TyId::new(999), PredId::new(0)),
        ],
    ));
    assert!(run(&m).0.is_empty());
}
#[test]
fn long_raw_nominal_names_and_full_row_type_display_preserve_every_original_byte() {
    let mut m = several();
    m.structs[0].name = "λ🦀'\n\0".repeat(1025);
    let errors = run(&m).0;
    assert!(
        matches!(&errors[0],ValidationError::InlineAggregateCycle{ty}if ty.contains(&m.structs[0].name))
    );
    let mut row = row_text();
    let Ty::Tuple(fields) = &mut row.types[0] else {
        panic!()
    };
    fields[1] = Ty::handle("λ🦀'\n".repeat(500), "rt::Name");
    assert_eq!(run(&row).0.len(), 1);
}
#[test]
fn deep_acyclic_chain_and_seeded_mixed_graphs_match_the_entire_original_scc_pass() {
    let mut m = Module::new("deep");
    for id in 0..512 {
        m.structs
            .push(strukt(id, vec![if id == 511 { Ty::U8 } else { s(id + 1) }]));
    }
    assert!(run(&m).0.is_empty());
    for seed in 0..24u32 {
        let mut m = Module::new("mixed");
        for id in 0..12u32 {
            m.structs.push(strukt(
                id,
                vec![
                    s((id * 7 + seed) % 15),
                    if (id + seed) % 3 == 0 {
                        Ty::Ref(Box::new(s(id)))
                    } else {
                        s((id * 11 + seed + 1) % 15)
                    },
                ],
            ));
        }
        run(&m);
    }
}
