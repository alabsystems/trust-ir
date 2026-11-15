// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_scalar_missing_and_unrelated_nominal_roots_name_no_handles() {
    let m = Module::new("");
    assert_eq!(
        run(
            &m,
            &[
                Ty::Bool,
                Ty::Ptr,
                Ty::Error,
                array(u32::MAX),
                Ty::Struct(StructId::new(77)),
                Ty::Func(FuncTyId::new(99)),
                Ty::Closure(ClosureTyId::new(3)),
                Ty::Dialect(Box::new(trust_ir::DialectTy::new("ns", "N", 1)))
            ],
            &[]
        )
        .0,
        ""
    );
}
#[test]
fn every_named_table_signature_capture_and_inline_edge_keeps_exact_closure() {
    let m = fixture();
    let roots = vec![
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Refine(TyId::new(1), PredId::new(1)),
        Ty::Set(TyId::new(0), trust_ir::SetRepr::Boxed),
        Ty::Sequence(TyId::new(0)),
        Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
        Ty::Vector(Box::new(array(0)), 4),
        Ty::Ref(Box::new(array(0))),
        Ty::RefMut(Box::new(array(0))),
        Ty::PtrConst(Box::new(array(0))),
        Ty::PtrMut(Box::new(array(0))),
        Ty::Rc(Box::new(array(0))),
        Ty::Tuple(vec![Ty::Bool, array(0)]),
    ];
    let out = run(&m, &roots, &[]).0;
    assert_eq!(
        out,
        [handle("A"), handle("B"), handle("M"), handle("Z")]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    );
}
#[test]
fn full_raw_identity_order_and_uniqueness_are_exact_not_normalized_or_name_only() {
    let m = Module::new("");
    let roots = vec![
        Ty::handle("λ\n\0\"", "rt::尾"),
        Ty::handle("same", "rt::B"),
        Ty::handle("same", "rt::A"),
        Ty::handle("same", "rt::B"),
        Ty::handle("", ""),
        Ty::handle("A", "\0"),
    ];
    let text = run(&m, &roots, &[]).0;
    assert_eq!(text.matches("handle<").count(), 5);
    assert!(text.find("rt::A").unwrap() < text.find("rt::B").unwrap());
}
#[test]
fn all_duplicate_named_definitions_contribute_even_when_the_indexed_one_is_scalar() {
    let mut m = Module::new("");
    m.structs = vec![structure(0, Ty::Bool), structure(0, handle("S"))];
    m.enums = vec![enumeration(0, Ty::Bool), enumeration(0, handle("E"))];
    m.records = vec![record(0, Ty::Bool), record(0, handle("R"))];
    let out = run(
        &m,
        &[
            Ty::Struct(StructId::new(0)),
            Ty::Enum(EnumId::new(0)),
            Ty::Record(RecordId::new(0)),
        ],
        &[],
    )
    .0;
    assert_eq!(
        out,
        [handle("E"), handle("R"), handle("S")]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    );
}
#[test]
fn cycles_share_seen_keys_by_namespace_and_include_closure_signature_and_capture_handles() {
    let mut m = Module::new("");
    m.types = vec![Ty::Struct(StructId::new(0))];
    m.structs = vec![structure(0, Ty::Enum(EnumId::new(0)))];
    m.enums = vec![enumeration(0, Ty::Record(RecordId::new(0)))];
    m.records = vec![record(0, Ty::Closure(ClosureTyId::new(0)))];
    m.closure_types = vec![ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![array(0), handle("Capture")],
    }];
    m.func_types = vec![FuncTy::unrecorded(
        vec![array(0)],
        vec![handle("Return")],
        false,
    )];
    let out = run(&m, &[array(0)], &[Ty::Func(FuncTyId::new(0))]).0;
    assert_eq!(
        out,
        [handle("Capture"), handle("Return")]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    );
}
#[test]
fn parameter_return_order_and_repeated_roots_keep_complete_sorted_union() {
    let m = fixture();
    let a = [Ty::Closure(ClosureTyId::new(0)), handle("Extra")];
    let b = [array(2), handle("Extra")];
    assert_eq!(run(&m, &a, &b).0, run(&m, &b, &a).0);
    assert_eq!(run(&m, &a, &a).0, run(&m, &a, &[]).0);
}
#[test]
fn long_actual_chain_has_no_cutoff_and_unrelated_definition_names_are_unread() {
    let mut m = Module::new("");
    m.types = (0..512).map(|i| array(i + 1)).collect();
    m.types.push(handle("Tail"));
    assert_eq!(run(&m, &[array(0)], &[]).0, handle("Tail").to_string());
    let a = fixture();
    let mut b = a.clone();
    b.name = "λ\0opaque".repeat(4096);
    for row in &mut b.structs {
        row.name = "raw name".repeat(4096);
    }
    for row in &mut b.enums {
        row.name = "enum name".repeat(4096);
    }
    for row in &mut b.records {
        row.name = "record name".repeat(4096);
    }
    assert_eq!(
        run(&a, &[Ty::Closure(ClosureTyId::new(0))], &[]).1.events,
        run(&b, &[Ty::Closure(ClosureTyId::new(0))], &[]).1.events
    );
}
