// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn exact_parameter_then_instruction_order_duplicate_blocks_and_one_error_per_node() {
    assert_eq!(
        parity(&fixture()),
        vec![
            diagnostic("function 'refinement' bb9 param 1".into()),
            diagnostic("function 'refinement' bb9 instruction 0".into()),
            diagnostic("function 'refinement' bb9 instruction 2".into()),
            diagnostic("function 'refinement' bb9 param 0".into()),
        ]
    );
}

#[test]
fn every_original_wrapper_and_tuple_recurses_but_empty_and_scalar_types_do_not() {
    let mut types = vec![
        refined(),
        Ty::Ref(Box::new(refined())),
        Ty::RefMut(Box::new(refined())),
        Ty::PtrConst(Box::new(refined())),
        Ty::PtrMut(Box::new(refined())),
        Ty::Vector(Box::new(refined()), 0),
        Ty::Rc(Box::new(refined())),
        Ty::Tuple(vec![Ty::Bool, Ty::Tuple(vec![Ty::Bool, refined()])]),
    ];
    let hits = types.len();
    types.extend([Ty::Tuple(vec![]), Ty::Bool, Ty::Never, Ty::Error]);
    assert_eq!(
        parity(&function("containers", vec![block(0, types, vec![])])).len(),
        hits
    );
}

#[test]
fn excluded_table_and_nominal_surfaces_never_follow_module_ids() {
    let types = vec![
        Ty::Array(TyId::new(0), 100),
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Sequence(TyId::new(0)),
        Ty::Struct(StructId::new(0)),
        Ty::Enum(EnumId::new(0)),
        Ty::Func(FuncTyId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
        Ty::FatPtr(trust_ir::FatPtrKind::Slice(TyId::new(0))),
    ];
    assert!(
        parity(&function(
            "ids",
            vec![block(0, types.clone(), vec![frame(types)])]
        ))
        .is_empty()
    );
}

#[test]
fn every_inline_field_is_inspected_after_first_hit_while_each_type_short_circuits() {
    let first = function(
        "fields",
        vec![block(0, vec![], vec![cast(refined(), Ty::Bool)])],
    );
    let second = function(
        "fields",
        vec![block(
            0,
            vec![],
            vec![cast(refined(), Ty::Tuple(vec![Ty::Bool; 4096]))],
        )],
    );
    let (a, shallow) = observed(&first);
    let (b, wide) = observed(&second);
    assert_eq!(a, b);
    assert_eq!(parity(&second).len(), 1);
    assert!(wide.work > shallow.work + 4096);

    let first = function(
        "short",
        vec![block(0, vec![Ty::Tuple(vec![refined(), Ty::Bool])], vec![])],
    );
    let second = function(
        "short",
        vec![block(
            0,
            vec![Ty::Tuple(vec![
                refined(),
                Ty::Tuple(vec![Ty::Bool; 100_000]),
            ])],
            vec![],
        )],
    );
    assert_eq!(observed(&first).1.events, observed(&second).1.events);
    assert_eq!(parity(&second).len(), 1);
}

#[test]
fn slot_and_dialect_lists_report_declared_types_but_exclude_attributes_and_names() {
    let mut dialect = trust_ir::dialect::DialectInst::new("refinement", "surface");
    dialect.result_tys = vec![Ty::Bool, refined(), refined()];
    dialect.attrs.push(trust_ir::dialect::AttrEntry {
        name: "ignored".repeat(4096),
        value: trust_ir::dialect::AttrValue::Ty(refined()),
    });
    let with_hits = function(
        "lists",
        vec![block(
            0,
            vec![],
            vec![
                frame(vec![refined(); 1024]),
                Inst::DialectOp(Box::new(dialect.clone())),
            ],
        )],
    );
    assert_eq!(parity(&with_hits).len(), 2);
    dialect.result_tys.clear();
    let excluded = function(
        "lists",
        vec![block(
            0,
            vec![],
            vec![frame(vec![]), Inst::DialectOp(Box::new(dialect))],
        )],
    );
    assert!(parity(&excluded).is_empty());
}

#[test]
fn names_are_copied_verbatim_across_utf8_boundaries_and_decimal_positions_are_exact() {
    let name = format!("{}'\n\0{}", "λ".repeat(700), "🦀".repeat(300));
    let f = function(
        &name,
        vec![block(
            u32::MAX,
            vec![refined(); 12],
            vec![Inst::Undef { ty: refined() }; 12],
        )],
    );
    let actual = parity(&f);
    assert_eq!(actual.len(), 24);
    assert_eq!(
        actual[11],
        diagnostic(format!("function '{name}' bb{} param 11", u32::MAX))
    );
    assert_eq!(
        actual[23],
        diagnostic(format!("function '{name}' bb{} instruction 11", u32::MAX))
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut text = String::new();
    work.number(u128::MAX, &mut text).unwrap();
    assert_eq!(text, u128::MAX.to_string());
    work.retire(text);
}

#[test]
fn moderate_nested_types_match_original_and_deep_borrowed_predicate_never_owns_input() {
    let mut ty = refined();
    for _ in 0..128 {
        ty = Ty::Tuple(vec![Ty::Ref(Box::new(ty)), Ty::Bool]);
    }
    assert_eq!(
        parity(&function("nested", vec![block(0, vec![ty], vec![])])).len(),
        1
    );
    let mut ty = refined();
    for _ in 0..50_000 {
        ty = Ty::Ref(Box::new(ty));
    }
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = Checking::default();
    assert!(state.contains(&ty, &mut work).unwrap());
    state.retire_scratch(&mut work);
    assert_eq!(state.frames.capacity(), 0);
    drop(state);
    // Test input disposal is caller-owned; avoid recursively dropping this
    // deliberately deep fixture without claiming it as subject retirement.
    while let Ty::Ref(child) = ty {
        ty = *child;
    }
}

#[test]
fn bodyless_empty_and_non_inline_function_signatures_remain_outside_this_constituent() {
    assert!(parity(&function("declaration", vec![])).is_empty());
    let mut f = function(
        "empty",
        vec![block(777, vec![], vec![Inst::Return { values: vec![] }])],
    );
    f.ty = FuncTyId::new(u32::MAX);
    f.proofs = vec![ProofAnnotation::Tainted];
    assert!(parity(&f).is_empty());
}
