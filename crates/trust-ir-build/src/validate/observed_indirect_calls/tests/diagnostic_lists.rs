// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! INDIRECT-R1: actual ordinary list wrappers, never a repaired oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

#[test]
fn closure_joined_list_wrappers_match_actual_ordinary_for_empty_and_nonempty_halves() {
    for (captures, params, returns) in [
        (vec![], vec![], vec![]),
        (vec![Ty::Bool], vec![], vec![Ty::U64]),
        (vec![], vec![Ty::Bool, Ty::U64], vec![]),
        (vec![Ty::Bool], vec![Ty::Bool, Ty::U64], vec![h()]),
    ] {
        let mut m = closure();
        m.closure_types[0].captures = captures.clone();
        m.func_types[1].params = params.clone();
        m.func_types[1].returns = returns.clone();
        m.functions[0].blocks[0].body[1].inst = call(10, 1, &[]);
        // Force physical-target disagreement independently of list emptiness.
        m.func_types[3] = FuncTy::unrecorded(vec![Ty::U8], vec![Ty::Bool], false);
        let errors = run(&m).0; // Whole actual original arm is the oracle.
        let found = errors
            .iter()
            .find_map(|e| match e {
                ValidationError::CallIndirectClosureTargetMismatch {
                    expected, actual, ..
                } => Some((expected, actual)),
                _ => None,
            })
            .unwrap();
        let joined: Vec<_> = captures.iter().chain(&params).cloned().collect();
        assert_eq!(
            found.0,
            &format!(
                "{}) -> ({}",
                format_ty_list(&joined),
                format_ty_list(&returns)
            )
        );
        assert_eq!(found.1, "(u8)) -> ((bool)");
    }
}

#[test]
fn typed_pointer_diagnostics_keep_original_double_wrappers_at_real_copy_reify_node() {
    for empty_lists in [false, true] {
        for copy_reify in [false, true] {
            let mut m = fixture();
            if empty_lists {
                m.func_types[1] = FuncTy::unrecorded(vec![], vec![], false);
                m.func_types[2] = FuncTy::unrecorded(vec![], vec![], false);
            }
            m.functions[1].ty = FuncTyId::new(2);
            let mut index = 1;
            if copy_reify {
                m.functions[0].blocks[0].body.insert(
                    1,
                    InstrNode::new(Inst::Copy {
                        ty: Ty::Func(FuncTyId::new(1)),
                        operand: v(10),
                    })
                    .with_result(v(11)),
                );
                m.functions[0].blocks[0].body.insert(
                    2,
                    InstrNode::new(Inst::Cast {
                        op: trust_ir::inst::CastOp::ReifyFnPointer,
                        src_ty: Ty::Func(FuncTyId::new(1)),
                        dst_ty: Ty::Ptr,
                        operand: v(11),
                    })
                    .with_result(v(12)),
                );
                index = 3;
            }
            m.functions[0].blocks[0].body[index].inst = call(
                if copy_reify { 12 } else { 10 },
                1,
                if empty_lists { &[] } else { &[0, 1] },
            );
            let errors = run_at(&m, 0, index).0;
            let [
                ValidationError::CallEdgeSignatureMismatch {
                    declared, actual, ..
                },
            ] = &errors[..]
            else {
                panic!("expected actual typed-pointer signature mismatch");
            };
            if empty_lists {
                assert_eq!(
                    declared,
                    "call functy.1 (()) -> (()); FnDef declares functy.1"
                );
                assert_eq!(actual, "target functy.2 (()) -> (())");
            } else {
                assert_eq!(
                    declared,
                    "call functy.1 ((bool, u64)) -> (()); FnDef declares functy.1"
                );
                assert_eq!(actual, "target functy.2 ((u64)) -> ((bool))");
            }
        }
    }
}

#[test]
fn wrapped_renderer_matches_actual_format_ty_list_for_empty_nested_and_unicode_data() {
    let rich = Ty::handle("é🦀name".repeat(300), "中runtime".repeat(300));
    for types in [
        vec![],
        vec![Ty::Bool],
        vec![
            Ty::Tuple(vec![Ty::U8, Ty::PtrConst(Box::new(Ty::Bool))]),
            rich,
        ],
    ] {
        let expected = format_ty_list(&types);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let (mut render, mut output) = (String::new(), String::new());
        render::wrapped_list(&types, &mut render, &mut output, &mut work).unwrap();
        assert_eq!(output, expected);
        assert_eq!(render.capacity(), 0);
        work.flat(take(&mut output));
        assert_eq!(output.capacity(), 0);
        assert!(s.first_refusal().is_none());
    }
}

#[test]
fn every_wrapper_callback_and_both_cumulative_caps_refuse_without_losing_held_strings() {
    let types = vec![Ty::handle("é🦀name".repeat(300), "中runtime".repeat(300))];
    let expected = format_ty_list(&types);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let (mut render, mut output) = (String::new(), String::new());
    render::wrapped_list(&types, &mut render, &mut output, &mut work).unwrap();
    let end = calls.get();
    assert_eq!(output, expected);
    work.flat(take(&mut render));
    work.flat(take(&mut output));
    drop(work);
    drop(s);
    let (mut saw_open, mut saw_child, mut saw_complete) = (false, false, false);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let (mut render, mut output) = (String::new(), String::new());
        assert_eq!(
            render::wrapped_list(&types, &mut render, &mut output, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw_open |= output.starts_with('(');
        saw_child |= !render.is_empty();
        saw_complete |= output == expected;
        work.flat(take(&mut render));
        work.flat(take(&mut output));
        assert_eq!(render.capacity() + output.capacity(), 0);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original indirect stop"
        );
        drop(work);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(saw_open && saw_child && saw_complete);
    for copy in [false, true] {
        let total = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(total)
        } else {
            o.work_cap = Some(total)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let (mut render, mut output) = (String::new(), String::new());
        render::wrapped_list(&types, &mut render, &mut output, &mut work).unwrap();
        assert_eq!(output, expected);
        assert_eq!(
            render::wrapped_list(&types, &mut render, &mut output, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        work.flat(take(&mut render));
        work.flat(take(&mut output));
        assert_eq!(render.capacity() + output.capacity(), 0);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
