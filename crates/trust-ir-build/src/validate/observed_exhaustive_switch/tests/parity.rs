// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn default_argument_parameter_body_and_selector_alias_errors_keep_exact_order() {
    assert_eq!(
        reasons(&parity(&fixture(), 32)),
        vec![
            "the default edge to bb1 passes 1 argument(s); a dead default carries none",
            "the default block bb1 has 1 parameter(s); a dead default has none",
            "the default block bb1 is not exactly [unreachable] (2 instruction(s))",
            "case values 0 and 4294967296 denote the same usize selector value",
        ]
    );
}
#[test]
fn ordinary_dead_default_and_distinct_cases_are_clean_for_all_integer_widths() {
    for ty in [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::U64,
        Ty::I128,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
    ] {
        let f = function(Some(ty), vec![Constant::Int(0), Constant::Int(1)]);
        for bits in [8, 16, 32, 64, 128, u32::MAX] {
            assert!(parity(&f, bits).is_empty());
        }
    }
}
#[test]
fn signed_unsigned_case_spelling_and_zero_or_oversized_pointer_widths_are_exact() {
    for ty in [Ty::I8, Ty::U8, Ty::Usize, Ty::Isize, Ty::Char] {
        let f = function(
            Some(ty),
            vec![
                Constant::Int(-1),
                Constant::U128(u128::MAX),
                Constant::Int(0),
                Constant::Int(1i128 << 32),
            ],
        );
        for bits in [0, 1, 8, 32, 64, 128, u32::MAX] {
            parity(&f, bits);
        }
    }
    let f = function(Some(Ty::Usize), vec![Constant::Int(0), Constant::Int(1)]);
    assert_eq!(parity(&f, 0).len(), 1);
}
#[test]
fn printed_syntactic_repeats_are_not_double_reported_and_first_stored_key_stays_authoritative() {
    let f = function(
        Some(Ty::Usize),
        vec![
            Constant::Int(0),
            Constant::U128(0),
            Constant::Int(0),
            Constant::Int(1i128 << 32),
            Constant::Int(2i128 << 32),
        ],
    );
    let errors = parity(&f, 32);
    assert_eq!(errors.len(), 2);
    assert!(
        reasons(&errors)
            .iter()
            .all(|reason| reason.starts_with("case values 0 and "))
    );
}
#[test]
fn unknown_and_noninteger_selectors_and_noninteger_case_payloads_keep_local_exemptions() {
    for ty in [
        None,
        Some(Ty::Bool),
        Some(Ty::Ptr),
        Some(Ty::Vector(Box::new(Ty::U32), 4)),
    ] {
        assert!(
            parity(
                &function(ty, vec![Constant::Int(0), Constant::Int(1i128 << 32)]),
                32
            )
            .is_empty()
        );
    }
    let f = function(
        Some(Ty::Usize),
        vec![
            Constant::Float(f64::NAN),
            Constant::Bytes {
                data: vec![255; 5000],
                utf8: false,
            },
            Constant::Bool(false),
        ],
    );
    assert!(parity(&f, 32).is_empty());
}
#[test]
fn first_duplicate_default_target_and_missing_target_keep_original_shape_boundary() {
    let mut f = function(Some(Ty::Usize), vec![]);
    let mut live = f.blocks[1].clone();
    live.body = vec![InstrNode::new(Inst::Return { values: vec![] })];
    f.blocks.push(live);
    assert!(parity(&f, 32).is_empty());
    f.blocks.swap(1, 2);
    assert_eq!(parity(&f, 32).len(), 1);
    let mut f = function(Some(Ty::Usize), vec![]);
    f.blocks.truncate(1);
    assert!(parity(&f, 32).is_empty());
}
#[test]
fn only_the_actual_last_flagged_terminator_constructs_a_lazy_value_map() {
    let mut f = fixture();
    if let Inst::Switch {
        exhaustive_enum_unreachable,
        ..
    } = &mut f.blocks[0].body[0].inst
    {
        *exhaustive_enum_unreachable = false;
    }
    for trailing in [false, true] {
        let mut f = f.clone();
        if trailing {
            if let Inst::Switch {
                exhaustive_enum_unreachable,
                ..
            } = &mut f.blocks[0].body[0].inst
            {
                *exhaustive_enum_unreachable = true;
            }
            f.blocks[0].body.push(InstrNode::new(Inst::NullPtr));
        }
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut s = State::default();
        s.walk(&f, 32, &mut work).unwrap();
        assert!(s.values.is_none());
        assert!(s.errors.is_empty());
        s.retire_scratch(&mut work);
        s.retire_errors(&mut work);
        assert!(empty(&s));
        assert!(parity(&f, 32).is_empty());
    }
    let f = function(None, vec![]);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    s.walk(&f, 32, &mut work).unwrap();
    assert!(s.values.is_some());
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
}
#[test]
fn standalone_complete_map_redefinitions_and_per_switch_seen_reset_are_preserved() {
    let mut f = function(
        Some(Ty::Usize),
        vec![Constant::Int(0), Constant::Int(1i128 << 32)],
    );
    f.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Undef { ty: Ty::U128 }).with_result(v(0)),
    );
    assert!(parity(&f, 32).is_empty());
    let mut f = function(
        Some(Ty::Usize),
        vec![Constant::Int(0), Constant::Int(1i128 << 32)],
    );
    let mut next = f.blocks[0].clone();
    next.id = BlockId::new(2);
    f.blocks.push(next);
    assert_eq!(parity(&f, 32).len(), 2);
}
