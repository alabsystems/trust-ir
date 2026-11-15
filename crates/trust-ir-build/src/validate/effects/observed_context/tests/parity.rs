// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn plain_and_panic_call_spelling_is_exact_for_raw_static_mnemonics() {
    for mnemonic in ["", "call", "assert_invoke", "λ\0'\n"] {
        for kind in [CallKind::Plain, CallKind::Panic] {
            let call = Call { mnemonic, kind };
            let mut o = Observer::default();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let parts = call.parts_observed(&mut s, site()).unwrap();
            let expected = match kind {
                CallKind::Plain => mnemonic.to_string(),
                CallKind::Panic => format!("{mnemonic} (its failure's panic call)"),
            };
            assert_eq!(text(&parts), expected);
            let Piece::Text(borrowed) = parts[0] else {
                panic!("mnemonic became a number")
            };
            assert_eq!(borrowed.as_ptr(), mnemonic.as_ptr());
        }
    }
}
#[test]
fn instruction_context_has_no_unrequested_suffix_and_all_seven_headers_are_fixed() {
    for mnemonic in ["", "atomic_load", "λ\0'\n"] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let parts = What::Instruction(mnemonic)
            .parts_observed(&mut s, site())
            .unwrap();
        assert_eq!(text(&parts), mnemonic);
        assert_eq!(parts.len(), 7);
        assert!(
            parts[1..]
                .iter()
                .all(|piece| matches!(piece, Piece::Text("")))
        );
    }
}
#[test]
fn parameter_context_keeps_exact_call_kind_side_and_unsigned_decimal_order() {
    for mnemonic in ["call", "assert_invoke", "λ\0"] {
        for kind in [CallKind::Plain, CallKind::Panic] {
            for side in [Side::Read, Side::Write] {
                for index in [0, 1, u32::MAX] {
                    let call = Call { mnemonic, kind };
                    let mut o = Observer::default();
                    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
                    let parts = What::Parameter { call, side, index }
                        .parts_observed(&mut s, site())
                        .unwrap();
                    let what = match kind {
                        CallKind::Plain => mnemonic.to_string(),
                        CallKind::Panic => format!("{mnemonic} (its failure's panic call)"),
                    };
                    let side = match side {
                        Side::Read => "reads",
                        Side::Write => "writes",
                    };
                    assert_eq!(
                        text(&parts),
                        format!("{what} (callee {side} *param{index})")
                    );
                }
            }
        }
    }
}
#[test]
fn all_parameter_and_missing_global_labels_match_the_actual_ordinary_root_label() {
    let module = fixture();
    for place in [
        EffectPlace::ParamPointee { index: 0 },
        EffectPlace::ParamPointee { index: u32::MAX },
        EffectPlace::Global(g(0)),
        EffectPlace::Global(g(1)),
        EffectPlace::Global(g(2)),
        EffectPlace::Global(g(u32::MAX)),
    ] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let parts = root_label_observed(place, &module, &mut s, site()).unwrap();
        assert_eq!(
            text(&parts),
            super::super::super::root_label(&place, &module)
        );
    }
}
#[test]
fn global_label_is_direct_storage_index_and_borrows_full_raw_name_without_validation() {
    for name in ["", "@raw λ\0'\n", " *param0 "] {
        let mut module = fixture();
        module.globals[0].name = "same".into();
        module.globals[1].name = name.into();
        module.globals[1].linkage = Linkage::Weak;
        module.globals[1].ty = Ty::Tuple(vec![Ty::U8; 100]);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let parts =
            root_label_observed(EffectPlace::Global(g(1)), &module, &mut s, site()).unwrap();
        drop(s);
        assert_eq!(text(&parts), format!("@{name}"));
        let Piece::Text(borrowed) = parts[1] else {
            panic!("raw name became number")
        };
        assert_eq!(borrowed.as_ptr(), module.globals[1].name.as_ptr());
        assert_eq!(borrowed.len(), name.len());
    }
}
#[test]
fn every_assert_class_and_overflow_operation_preserves_operands_then_location() {
    let kinds = kinds();
    assert_eq!(kinds.len(), 14);
    for kind in kinds {
        for location in [
            PanicLocation::Global(g(u32::MAX)),
            PanicLocation::Value(v(0)),
        ] {
            let expected = ordinary_args(&kind, location);
            let mut o = Observer::default();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let args = Arguments::panic_observed(&kind, location, &mut s, site()).unwrap();
            for index in [0, 1, 2, 3, usize::MAX] {
                assert_eq!(
                    key(args.get_observed(index, &mut s, site()).unwrap()),
                    key(expected.get(index).copied())
                );
            }
        }
    }
}
#[test]
fn duplicate_panic_operands_are_preserved_and_global_location_never_becomes_value() {
    for kind in [
        AssertKind::BoundsCheck {
            index: v(7),
            len: v(7),
        },
        AssertKind::MisalignedPtr {
            required: v(u32::MAX),
            found: v(u32::MAX),
        },
    ] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let args =
            Arguments::panic_observed(&kind, PanicLocation::Global(g(7)), &mut s, site()).unwrap();
        assert_eq!(
            key(args.get_observed(0, &mut s, site()).unwrap()),
            key(args.get_observed(1, &mut s, site()).unwrap())
        );
        assert_eq!(
            key(args.get_observed(2, &mut s, site()).unwrap()),
            Some((1, 7))
        );
    }
}
#[test]
fn borrowed_value_argument_slots_match_the_discarded_ordinary_vec_at_every_bound() {
    for values in [Vec::new(), vec![v(9), v(0), v(9), v(u32::MAX)]] {
        let expected = values.iter().copied().map(Arg::Value).collect::<Vec<_>>();
        let args = Arguments::Values(&values);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        for index in [0, 1, 2, 3, 4, usize::MAX] {
            assert_eq!(
                key(args.get_observed(index, &mut s, site()).unwrap()),
                key(expected.get(index).copied())
            );
        }
    }
}
#[test]
fn element_slot_models_exactly_one_untraceable_argument() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    for index in [0, 1, 2, usize::MAX] {
        assert_eq!(
            key(Arguments::ElementSlot
                .get_observed(index, &mut s, site())
                .unwrap()),
            if index == 0 { Some((2, 0)) } else { None }
        );
    }
}
#[test]
fn global_name_bytes_deep_type_and_unselected_storage_tail_are_not_walked_or_cloned() {
    let small = fixture();
    let base = trace(Query::Label(EffectPlace::Global(g(0)), &small));
    let mut huge = small.clone();
    huge.globals[0].name = "rawλ\0".repeat(100000);
    huge.globals[0].ty = Ty::Tuple(vec![Ty::Tuple(vec![Ty::U8]); 3000]);
    huge.globals.extend((0..1000).map(|_| global("tail")));
    assert_eq!(
        base.events,
        trace(Query::Label(EffectPlace::Global(g(0)), &huge)).events
    );
}
#[test]
fn unqueried_value_tail_and_panic_location_have_no_argument_lookup_work() {
    let small = [v(7)];
    let mut huge = vec![v(7)];
    huge.extend(vec![v(u32::MAX); 100000]);
    assert_eq!(
        trace(Query::Get(Arguments::Values(&small), 0)).events,
        trace(Query::Get(Arguments::Values(&huge), 0)).events
    );
    let make = |location| Arguments::Panic {
        operands: Some([v(7), v(9)]),
        location,
    };
    assert_eq!(
        trace(Query::Get(make(PanicLocation::Global(g(u32::MAX))), 0)).events,
        trace(Query::Get(make(PanicLocation::Value(v(0))), 0)).events
    );
}
