// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; exact original switch-selector callback is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn original(m: &Module, f: &Function) -> BTreeMap<u32, Ty> {
    let catalog = ModuleFunctionCatalog::new(m);
    super::super::super::build_module_value_types_with(f, |node| match &node.inst {
        Inst::Call { callee, .. }
        | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => catalog
            .unique(*callee)
            .and_then(|f| m.func_type(f.ty))
            .map(|s| s.returns.clone())
            .unwrap_or_default(),
        _ => node.result_tys(m),
    })
}
fn observed(m: &Module, f: &Function) -> (ObservedValueTypes, Observer) {
    let catalog = ModuleFunctionCatalog::new(m);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = build_catalog_value_types_observed(f, &catalog, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    (out, o)
}
fn parity_catalog(m: &Module, f: &Function) -> BTreeMap<u32, Ty> {
    let expected = original(m, f);
    let (out, o) = observed(m, f);
    let rows: BTreeMap<_, _> = out.rows.into_iter().collect();
    assert_eq!(rows, expected);
    assert!(o.events.iter().all(|e| e.site == site()));
    rows
}
fn data() -> (Module, Function) {
    let mut m = Module::new("catalog");
    m.func_types = vec![
        FuncTy::unrecorded(vec![], vec![Ty::U8], false),
        FuncTy::unrecorded(vec![], vec![Ty::Bool, Ty::U64], false),
    ];
    m.functions = vec![
        Function::new(FuncId::new(900), "sparse", FuncTyId::new(1), b(0)),
        Function::new(FuncId::new(0), "zero", FuncTyId::new(0), b(0)),
    ];
    let f = function(vec![
        node(
            Inst::Call {
                callee: FuncId::new(900),
                args: vec![],
            },
            &[1, 2, 3],
        ),
        node(
            Inst::CallCannotUnwind {
                callee: FuncId::new(0),
                args: vec![],
            },
            &[4],
        ),
        node(
            Inst::Invoke {
                callee: FuncId::new(900),
                args: vec![],
                normal_dest: b(1),
                normal_args: vec![],
                unwind_dest: b(2),
            },
            &[6, 7],
        ),
        node(
            Inst::Call {
                callee: FuncId::new(999),
                args: vec![],
            },
            &[5],
        ),
    ]);
    (m, f)
}
#[test]
fn actual_sparse_and_duplicate_direct_calls_use_unique_catalog_returns() {
    let (mut m, f) = data();
    assert_eq!(parity_catalog(&m, &f).get(&1), Some(&Ty::Bool));
    let mut duplicate = m.functions[0].clone();
    duplicate.ty = FuncTyId::new(0);
    m.functions.push(duplicate);
    let rows = parity_catalog(&m, &f);
    assert!(
        !rows.contains_key(&1)
            && !rows.contains_key(&2)
            && !rows.contains_key(&3)
            && !rows.contains_key(&6)
            && !rows.contains_key(&7)
    );
    assert_eq!(rows.get(&4), Some(&Ty::U8));
}
#[test]
fn ordinary_module_index_preference_and_catalog_ambiguity_remain_distinct() {
    let (mut m, _) = data();
    let duplicate = m.functions[1].clone();
    m.functions.push(duplicate);
    let f = function(vec![node(
        Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        },
        &[42],
    )]);
    assert_eq!(
        super::super::super::build_module_value_types(&f, &m).get(&42),
        Some(&Ty::U8)
    );
    assert!(parity_catalog(&m, &f).is_empty());
    super::parity(&f, Some(&m));
}
#[test]
fn unresolved_direct_call_preserves_existing_last_known_block_parameter_type() {
    let (mut m, mut f) = data();
    let duplicate = m.functions[0].clone();
    m.functions.push(duplicate);
    f.blocks[0].params.push((v(1), Ty::I16));
    assert_eq!(parity_catalog(&m, &f).get(&1), Some(&Ty::I16));
    m.func_types.clear();
    assert_eq!(parity_catalog(&m, &f).get(&1), Some(&Ty::I16));
}
#[test]
fn all_nondirect_plans_and_original_borrow_phase_keep_module_semantics() {
    let (m, _) = data();
    let mut f = fixture();
    f.blocks[0].body.extend([
        node(
            Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            },
            &[40, 41, 42],
        ),
        node(
            Inst::CallIndirect {
                callee: v(99),
                sig: FuncTyId::new(1),
                args: vec![],
                calling_conv: CallingConv::C,
            },
            &[43, 44, 45],
        ),
        node(
            Inst::DialectOp(Box::new(
                trust_ir::dialect::DialectInst::new("data", "op")
                    .with_result_tys([Ty::U16, Ty::Bool]),
            )),
            &[46, 47, 48],
        ),
    ]);
    let expected = super::super::super::build_module_value_types(&f, &m);
    assert_eq!(parity_catalog(&m, &f), expected);
}
#[test]
fn every_actual_catalog_lookup_clone_commit_borrow_and_publication_callback_refuses() {
    let (m, f) = data();
    let (_, baseline) = observed(&m, &f);
    let catalog = ModuleFunctionCatalog::new(&m);
    for stop in 1..=baseline.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            build_catalog_value_types_observed(&f, &catalog, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.first_refusal().unwrap().cause, "original value stop");
        drop(s);
        assert_eq!(&o.events[..stop], &baseline.events[..stop]);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn repeated_catalog_maps_share_both_original_cumulative_budgets() {
    let (m, f) = data();
    let catalog = ModuleFunctionCatalog::new(&m);
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let a = build_catalog_value_types_observed(&f, &catalog, &mut s, site()).unwrap();
    let b = build_catalog_value_types_observed(&f, &catalog, &mut s, site()).unwrap();
    drop(s);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(baseline.work - 1),
            byte_cap: copy.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = build_catalog_value_types_observed(&f, &catalog, &mut s, site()).unwrap();
        assert!(matches!(
            build_catalog_value_types_observed(&f, &catalog, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "bytes" } else { "work" }
        );
        let _ = out.retire_observed(&mut s, site());
    }
    let mut cleanup = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut cleanup);
    a.retire_observed(&mut s, site()).unwrap();
    b.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn complete_catalog_result_clone_stays_pending_before_next_parent_lookup() {
    let (mut m, _) = data();
    m.func_types[1].returns = vec![Ty::Tuple(vec![Ty::U64; 24])];
    let f = function(vec![node(
        Inst::Call {
            callee: FuncId::new(900),
            args: vec![],
        },
        &[1],
    )]);
    let catalog = ModuleFunctionCatalog::new(&m);
    use std::{cell::Cell, rc::Rc};
    struct Counted {
        inner: Observer,
        calls: Rc<Cell<usize>>,
    }
    impl ExecutionObserver for Counted {
        type Refusal = &'static str;
        fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
            self.calls.set(self.calls.get() + 1);
            self.inner.admit(e)
        }
    }
    let calls = Rc::new(Cell::new(0));
    let mut baseline = Counted {
        inner: Observer::default(),
        calls: calls.clone(),
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state
        .walk(&f, Context::Catalog(&catalog), &mut work)
        .unwrap();
    let end = calls.get();
    state.retire_scratch(&mut work);
    state.output.retire(&mut work);
    drop(work);
    drop(s);
    let mut saw = false;
    for stop in 1..=end {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let result = state.walk(&f, Context::Catalog(&catalog), &mut work);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        {
            if matches!(&state.pending,Some(Ty::Tuple(v))if v.len()==24) {
                saw = true;
                assert!(state.output.rows.is_empty());
            }
            state.retire_scratch(&mut work);
            state.output.retire(&mut work);
            assert!(state.pending.is_none());
            assert_eq!(state.output.rows.capacity(), 0);
        }
    }
    assert!(saw);
}
#[test]
fn successful_owned_map_retirement_has_original_terminal_and_sticky_stop() {
    let (m, f) = data();
    let catalog = ModuleFunctionCatalog::new(&m);
    let (_, baseline) = observed(&m, &f);
    for refuse in [false, true] {
        let mut o = Observer {
            stop: refuse.then_some(baseline.events.len() + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = build_catalog_value_types_observed(&f, &catalog, &mut s, site()).unwrap();
        let result = out.retire_observed(&mut s, site());
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(s.first_refusal().unwrap().cause, "original value stop");
        } else {
            result.unwrap();
        }
        drop(s);
        if refuse {
            assert!(
                o.events[baseline.events.len()..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        } else {
            let e = o.events.last().unwrap();
            assert_eq!(
                (e.phase, e.work, e.copy_bytes),
                (ExecutionPhase::Publication, 1, 0)
            );
        }
    }
}
