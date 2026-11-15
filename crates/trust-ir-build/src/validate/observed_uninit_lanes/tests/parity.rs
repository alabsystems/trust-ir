// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn empty_modules_bodyless_functions_absent_initializers_and_other_instructions_keep_empty_results()
{
    assert!(run(&Module::new("")).0.is_empty());
    let mut m = fixture(Ty::U8, Constant::Int(1));
    m.globals.push(global("absent", None));
    m.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Return { values: vec![] })];
    assert!(run(&m).0.is_empty());
    m.functions[0].blocks.clear();
    assert!(run(&m).0.is_empty());
}
#[test]
fn only_direct_struct_or_tuple_aggregate_lanes_may_be_uninit() {
    for ty in [
        Ty::Struct(StructId::new(99)),
        Ty::Tuple(vec![Ty::Bool, Ty::U8]),
    ] {
        let m = fixture(
            ty.clone(),
            Constant::Aggregate(vec![Constant::Uninit, Constant::Int(1), Constant::Uninit]),
        );
        assert!(run(&m).0.is_empty());
        for value in carriers(Constant::Uninit) {
            let m = fixture(ty.clone(), Constant::Aggregate(vec![value]));
            assert_eq!(run(&m).0.len(), 1);
        }
        assert_eq!(run(&fixture(ty, Constant::Uninit)).0.len(), 1);
    }
}
#[test]
fn all_other_declared_types_and_every_recursive_carrier_keep_the_original_full_diagnostic() {
    for ty in [
        Ty::U8,
        Ty::Ptr,
        Ty::Enum(trust_ir::value::EnumId::new(0)),
        Ty::Record(trust_ir::value::RecordId::new(0)),
        Ty::Closure(trust_ir::value::ClosureTyId::new(0)),
        Ty::Refine(
            trust_ir::value::TyId::new(0),
            trust_ir::value::PredId::new(0),
        ),
        Ty::Array(trust_ir::value::TyId::new(0), 1),
        Ty::Ref(Box::new(Ty::Tuple(vec![Ty::U8]))),
    ] {
        for value in carriers(Constant::Uninit) {
            assert_eq!(run(&fixture(ty.clone(), value)).0.len(), 1);
        }
    }
}
#[test]
fn all_uninit_free_leaves_and_containers_are_accepted_without_formatting_unused_payloads() {
    let leaves = vec![
        Constant::Int(i128::MIN),
        Constant::U128(u128::MAX),
        Constant::Float(f64::NAN),
        Constant::Float(-0.0),
        Constant::Bool(true),
        Constant::Bytes {
            data: vec![0; 3000],
            utf8: false,
        },
        Constant::SymbolAddr {
            symbol: "uninit\0TAIL".repeat(400),
            addend: i64::MIN,
        },
        Constant::FnDef(FuncId::new(u32::MAX)),
        Constant::PhantomData,
    ];
    for leaf in leaves {
        assert!(run(&fixture(Ty::U8, leaf.clone())).0.is_empty());
        for value in carriers(leaf) {
            assert!(run(&fixture(Ty::U8, value)).0.is_empty());
        }
    }
}
#[test]
fn all_global_initializers_refuse_uninit_even_when_a_direct_lane_would_be_legal_in_const() {
    for value in std::iter::once(Constant::Uninit).chain(carriers(Constant::Uninit)) {
        let mut m = Module::new("");
        m.globals.push(global("raw'λ\n\0TAIL", Some(value)));
        let errors = run(&m).0;
        assert_eq!(
            errors,
            vec![ValidationError::ConstTypeMismatch {
                location: "global 'raw'λ\n\0TAIL'".into(),
                expected: EXPECTED.into(),
                actual: "an unwritten lane (uninit) in a global initializer".into()
            }]
        );
    }
}
#[test]
fn switch_first_hit_is_one_error_and_skips_all_later_case_payloads() {
    let mut m = fixture(Ty::U8, Constant::Int(1));
    m.functions[0].blocks[0].body = vec![InstrNode::new(switch(vec![
        Constant::Int(1),
        Constant::Uninit,
        Constant::Uninit,
    ]))];
    let (errors, a, cut_a) = run(&m);
    assert_eq!(errors.len(), 1);
    let mut huge = m.clone();
    if let Inst::Switch { cases, .. } = &mut huge.functions[0].blocks[0].body[0].inst {
        cases[2].value = Constant::Aggregate(vec![Constant::Int(1); 20_000]);
    }
    let (other, b, cut_b) = run(&huge);
    assert_eq!(other, errors);
    assert_eq!(cut_a, cut_b);
    assert_eq!(a.events, b.events);
}
#[test]
fn globals_then_function_block_instruction_order_and_raw_full_locations_match_ordinary() {
    let mut m = fixture(Ty::U8, Constant::Uninit);
    m.globals.push(global("first", Some(Constant::Uninit)));
    m.globals.push(global("second", Some(Constant::Uninit)));
    m.functions[0].blocks[0]
        .body
        .push(InstrNode::new(switch(vec![Constant::Uninit])));
    let mut b = Block::new(BlockId::new(u32::MAX));
    b.body.push(InstrNode::new(Inst::Const {
        ty: Ty::Bool,
        value: Constant::Uninit,
    }));
    m.functions[0].blocks.push(b);
    let errors = run(&m).0;
    assert_eq!(errors.len(), 5);
    assert!(
        matches!(&errors[0],ValidationError::ConstTypeMismatch{location,..}if location=="global 'first'")
    );
    assert!(
        matches!(&errors[4],ValidationError::ConstTypeMismatch{location,..}if location==&format!("function '{}' bb{}",m.functions[0].name,u32::MAX))
    );
}
#[test]
fn invalid_constant_diagnostic_keeps_all_float_debug_nested_type_and_raw_carrier_text() {
    for float in [
        0.0,
        -0.0,
        1.25,
        1e300,
        1e-300,
        f64::MIN_POSITIVE,
        f64::MAX,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
    ] {
        let value = Constant::Aggregate(vec![
            Constant::Float(float),
            Constant::SymbolAddr {
                symbol: "rawλ'\n\0TAIL".into(),
                addend: -7,
            },
            Constant::Uninit,
        ]);
        let ty = Ty::Ref(Box::new(Ty::Tuple(vec![Ty::U8, Ty::Bool])));
        let errors = run(&fixture(ty.clone(), value.clone())).0;
        assert!(
            matches!(&errors[0],ValidationError::ConstTypeMismatch { actual,.. }if actual==&format!("{ty} constant {value} carries uninit outside a direct lane"))
        );
    }
}
#[test]
fn splat_length_and_ignored_record_names_never_expand_or_change_membership_work() {
    let a = fixture(
        Ty::U8,
        Constant::Splat {
            elem: Box::new(Constant::Uninit),
            len: 2,
        },
    );
    let mut b = a.clone();
    if let Inst::Const {
        value: Constant::Splat { len, .. },
        ..
    } = &mut b.functions[0].blocks[0].body[0].inst
    {
        *len = u64::MAX;
    }
    // Membership has the same trace; full invalid diagnostics intentionally spell len.
    let values = [
        Constant::Record(vec![("x".into(), Constant::Int(1))]),
        Constant::Record(vec![("x".repeat(100_000), Constant::Int(1))]),
    ];
    let measure = |value: &Constant| {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        assert!(!state.mentions(value, &mut work).unwrap());
        assert!(empty(&state));
        drop(state);
        drop(work);
        drop(session);
        observer.events
    };
    assert_eq!(measure(&values[0]), measure(&values[1]));
    run(&a);
    run(&b);
}
