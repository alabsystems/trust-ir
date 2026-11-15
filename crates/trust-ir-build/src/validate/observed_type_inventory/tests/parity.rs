// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn full_twenty_two_occurrence_errors_keep_exact_original_locations_and_order() {
    let (out, census) = run(&fixture()).0;
    let locations: Vec<_> = out.iter().map(error_location).collect();
    assert_eq!(
        locations,
        vec![
            "type.0",
            "type.0",
            "struct 'S' field 0",
            "struct 'S' field 1",
            "record 'R' field 0",
            "enum 'E' variant 'V' field 0",
            "enum 'E' variant 'V' field 1",
            "closure.0",
            "closure.0 capture 0",
            "closure.0 capture 1",
            "functy.0 param 0",
            "functy.0 param 1",
            "functy.0 return 0",
            "global 'G'",
            "drop_glue row 0",
            "function 'f' bb0",
            "function 'f' bb0",
            "function 'f' bb0",
            "function 'f' bb0",
            "function 'f' bb0",
            "function 'f' bb0",
            "function 'f' bb0"
        ]
    );
    assert_eq!(
        census,
        NominalCensus {
            dialect: true,
            handle: true
        }
    );
}
#[test]
fn empty_and_closed_primitive_inputs_return_empty_errors_and_false_census() {
    assert_eq!(run(&Module::new("")).0, (vec![], NominalCensus::default()));
    let mut m = Module::new("");
    m.types = vec![
        Ty::Bool,
        Ty::I64,
        Ty::Tuple(vec![
            Ty::Ref(Box::new(Ty::U8)),
            Ty::Vector(Box::new(Ty::F32), 4),
        ]),
    ];
    assert_eq!(run(&m).0, (vec![], NominalCensus::default()));
}
#[test]
fn cyclic_table_ids_are_checked_once_without_following_the_reference_graph() {
    let mut m = Module::new("");
    m.types = vec![Ty::Sequence(TyId::new(0)), Ty::Array(TyId::new(1), 1)];
    let (out, o, _) = run(&m);
    assert_eq!(out, (vec![], NominalCensus::default()));
    assert!(o.events.len() < 1000);
}
#[test]
fn deep_inline_walk_is_iterative_and_successful_input_disposal_stays_with_caller() {
    let mut ty = d();
    for _ in 0..2048 {
        ty = Ty::Ref(Box::new(ty));
    }
    let mut m = Module::new("");
    m.types.push(ty);
    assert_eq!(run(&m).0.0.len(), 1);
    let mut ty = m.types.pop().unwrap();
    loop {
        match ty {
            Ty::Ref(inner) => ty = *inner,
            Ty::Struct(id) => {
                assert_eq!(id, StructId::new(99));
                break;
            }
            _ => panic!("fixture changed"),
        }
    }
}
#[test]
fn all_eleven_location_formats_keep_raw_names_and_extreme_decimal_indices() {
    let name = "raw ' λ\0尾";
    let variant = "variant ' λ\0尾";
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    for (source, expected) in [
        (Location::Type(usize::MAX), format!("type.{}", usize::MAX)),
        (
            Location::Struct(name, 7),
            format!("struct '{name}' field 7"),
        ),
        (
            Location::Record(name, 8),
            format!("record '{name}' field 8"),
        ),
        (
            Location::Enum(name, variant, 9),
            format!("enum '{name}' variant '{variant}' field 9"),
        ),
        (
            Location::Closure(usize::MAX),
            format!("closure.{}", usize::MAX),
        ),
        (Location::Capture(7, 8), "closure.7 capture 8".into()),
        (Location::Parameter(7, 8), "functy.7 param 8".into()),
        (Location::Return(7, 8), "functy.7 return 8".into()),
        (Location::Global(name), format!("global '{name}'")),
        (
            Location::DropGlue(usize::MAX),
            format!("drop_glue row {}", usize::MAX),
        ),
        (
            Location::Function(name, u32::MAX),
            format!("function '{name}' bb{}", u32::MAX),
        ),
    ] {
        state.location(source, &mut w).unwrap();
        assert_eq!(state.location, expected);
    }
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn actual_typed_dialect_attributes_follow_results_and_include_inline_children() {
    let mut op = DialectInst::new("unread", "unread");
    op.result_tys.push(d());
    op.attrs = vec![
        AttrEntry {
            name: "raw".into(),
            value: AttrValue::Bytes(vec![0; 100]),
        },
        AttrEntry {
            name: "typed".into(),
            value: AttrValue::Ty(Ty::Tuple(vec![
                invalid(),
                Ty::handle("NotPinned", "untrusted::NotPinned"),
            ])),
        },
    ];
    let mut m = Module::new("");
    m.functions
        .push(function("f", vec![Inst::DialectOp(Box::new(op))], vec![]));
    let (out, c) = run(&m).0;
    assert_eq!(out.len(), 3);
    assert!(matches!(
        &out[0],
        ValidationError::DanglingTypeReference { .. }
    ));
    assert!(matches!(
        &out[1],
        ValidationError::InvalidDialectType { .. }
    ));
    assert!(matches!(
        &out[2],
        ValidationError::UntrustedHandleRuntime { .. }
    ));
    assert!(c.dialect && c.handle);
}
#[test]
fn unrelated_instruction_operands_names_and_non_type_attributes_are_not_walked() {
    let mut op = DialectInst::new("raw", "raw");
    op.attrs.push(AttrEntry {
        name: "raw".into(),
        value: AttrValue::Str("short".into()),
    });
    let mut m = Module::new("");
    m.functions
        .push(function("f", vec![Inst::DialectOp(Box::new(op))], vec![]));
    let (_, small, _) = run(&m);
    let Inst::DialectOp(op) = &mut m.functions[0].blocks[0].body[0].inst else {
        panic!("fixture")
    };
    op.dialect = "unused λ\0".repeat(10000);
    op.op = "unused 尾\0".repeat(10000);
    op.operands = vec![ValueId::new(u32::MAX); 10000];
    op.attrs[0].name = "unused λ\0".repeat(10000);
    op.attrs[0].value = AttrValue::Str("unused 尾\0".repeat(10000));
    let (_, large, _) = run(&m);
    assert_eq!(small.events, large.events);
}
#[test]
fn bare_closure_function_error_precedes_capture_errors_and_signature_rows() {
    let mut m = Module::new("");
    m.closure_types.push(ClosureTy {
        func: FuncTyId::new(99),
        captures: vec![d()],
    });
    m.func_types
        .push(FuncTy::unrecorded(vec![d()], vec![d()], false));
    let (out, _) = run(&m).0;
    assert_eq!(
        out.iter().map(error_location).collect::<Vec<_>>(),
        vec![
            "closure.0",
            "closure.0 capture 0",
            "functy.0 param 0",
            "functy.0 return 0"
        ]
    );
}
#[test]
fn unused_duplicate_physical_definition_rows_are_not_deduplicated() {
    let mut m = Module::new("");
    let def = strukt("raw λ\0", vec![field("ignored", d())]);
    m.structs = vec![def.clone(), def];
    let (out, _) = run(&m).0;
    assert_eq!(out.len(), 2);
    assert_eq!(out[0], out[1]);
}
#[test]
fn every_inline_container_preserves_preorder_while_table_references_stay_leaves() {
    let mut m = Module::new("");
    m.types = vec![Ty::Tuple(vec![
        Ty::Ref(Box::new(d())),
        Ty::RefMut(Box::new(d())),
        Ty::PtrConst(Box::new(d())),
        Ty::PtrMut(Box::new(d())),
        Ty::Rc(Box::new(d())),
        Ty::Vector(Box::new(d()), 4),
        Ty::Tuple(vec![invalid()]),
    ])];
    let (out, c) = run(&m).0;
    assert_eq!(out.len(), 7);
    assert!(
        out[..6]
            .iter()
            .all(|e| matches!(e, ValidationError::DanglingTypeReference { .. }))
    );
    assert!(matches!(
        &out[6],
        ValidationError::InvalidDialectType { .. }
    ));
    assert!(c.dialect && !c.handle);
}
