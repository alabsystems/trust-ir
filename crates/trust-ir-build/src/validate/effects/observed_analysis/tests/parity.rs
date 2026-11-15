// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn absent_summary_effects_and_bodyless_declarations_remain_unchecked_empty_results() {
    let (m, mut f) = fixture(vec![node(load(99), &[])]);
    f.summary = None;
    assert!(run(&m, &f, ImportPolicy::Structural).0.is_empty());
    f.summary = Some(FunctionSummary::new());
    assert!(run(&m, &f, ImportPolicy::Refuse).0.is_empty());
    f.summary.as_mut().unwrap().effects = Some(EffectSummary::pure());
    f.blocks.clear();
    assert!(run(&m, &f, ImportPolicy::Refuse).0.is_empty());
}
#[test]
fn every_current_instruction_shape_preserves_the_complete_ordinary_diagnostics() {
    let all = witnesses::all();
    assert_eq!(all.len(), 67);
    let names = all
        .iter()
        .map(|i| format!("{:?}", i.shape()))
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(names.len(), 67);
    for instruction in all {
        let (m, f) = fixture(vec![node(instruction, &[9])]);
        run(&m, &f, ImportPolicy::Structural);
        run(&m, &f, ImportPolicy::Refuse);
    }
}
#[test]
fn locals_are_exempt_while_formal_and_raw_global_roots_require_their_exact_places() {
    let (m, mut f) = fixture(vec![
        node(alloca(), &[3]),
        node(load(3), &[]),
        node(load(1), &[]),
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(7),
            },
            &[4],
        ),
        node(store(4), &[]),
    ]);
    let out = run(&m, &f, ImportPolicy::Structural).0;
    assert_eq!(out.len(), 2);
    f.summary.as_mut().unwrap().effects = Some(
        EffectSummary::pure()
            .reading(EffectSet::of([p(0)]))
            .writing(EffectSet::of([g(7)])),
    );
    assert!(run(&m, &f, ImportPolicy::Structural).0.is_empty());
}
#[test]
fn first_reason_blocks_and_canonical_place_order_survive_reverse_access_order() {
    let (m, mut f) = fixture(vec![
        node(load(2), &[]),
        node(load(1), &[]),
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(7),
            },
            &[4],
        ),
        node(load(4), &[]),
        node(load(1), &[]),
    ]);
    f.blocks[0].id = BlockId::new(u32::MAX);
    f.entry = BlockId::new(u32::MAX);
    let out = run(&m, &f, ImportPolicy::Structural).0;
    assert_eq!(out.len(), 3);
    for error in &out {
        assert!(
            matches!(error,ValidationError::EffectSummaryViolated {block,..} if *block==u32::MAX)
        );
    }
    assert!(
        matches!(&out[0],ValidationError::EffectSummaryViolated {effect:"reads",inst,..} if inst=="load through *param0")
    );
    assert!(
        matches!(&out[1],ValidationError::EffectSummaryViolated {inst,..} if inst=="load through *param1")
    );
    assert!(
        matches!(&out[2],ValidationError::EffectSummaryViolated {inst,..} if inst=="load through global #7")
    );
}
#[test]
fn everything_suppresses_named_place_errors_in_either_access_order_without_losing_flags() {
    for reverse in [false, true] {
        let mut nodes = vec![node(load(1), &[]), node(load(99), &[])];
        if reverse {
            nodes.reverse()
        }
        nodes.push(node(
            Inst::HeapAlloc {
                ty: Ty::U32,
                count: None,
                align: None,
                origin: AllocOrigin::RustHeap,
            },
            &[4],
        ));
        let (m, f) = fixture(nodes);
        let out = run(&m, &f, ImportPolicy::Structural).0;
        assert_eq!(out.len(), 2);
        assert!(
            matches!(&out[0],ValidationError::EffectSummaryViolated {effect:"reads",inst,..} if inst.ends_with(", which needs reads: Everything"))
        );
        assert!(
            matches!(&out[1],ValidationError::EffectSummaryViolated {effect:"allocates",inst,..} if inst=="heapalloc")
        );
    }
}
#[test]
fn all_reads_writes_and_four_flag_errors_keep_original_order_and_complete_top_reasons() {
    let (m, f) = fixture(vec![node(
        Inst::Call {
            callee: FuncId::new(99),
            args: vec![],
        },
        &[],
    )]);
    let out = run(&m, &f, ImportPolicy::Refuse).0;
    let names = out
        .iter()
        .map(|e| match e {
            ValidationError::EffectSummaryViolated { effect, .. } => *effect,
            _ => panic!("other error"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        names,
        ["reads", "writes", "allocates", "frees", "may_unwind", "io"]
    );
    for e in out {
        assert!(
            matches!(e,ValidationError::EffectSummaryViolated {function,inst,..} if function=="bodyλ\0" && inst.starts_with("call to #99, which has no admissible effect summary (havoc)"))
        );
    }
}
#[test]
fn an_everything_and_all_flags_declaration_admits_unknown_body_effects_as_an_upper_bound() {
    let (m, mut f) = fixture(vec![
        node(dialect(2), &[]),
        node(Inst::Release { ptr: v(99) }, &[]),
    ]);
    f.summary.as_mut().unwrap().effects = Some(EffectSummary::top());
    assert!(run(&m, &f, ImportPolicy::Structural).0.is_empty());
}
#[test]
fn root_cycles_duplicates_and_reentered_entry_keep_the_original_conservative_havoc() {
    let (m, mut f) = fixture(vec![
        node(
            Inst::Copy {
                ty: Ty::Ptr,
                operand: v(9),
            },
            &[9],
        ),
        node(load(9), &[]),
        node(alloca(), &[1]),
        node(load(1), &[]),
    ]);
    run(&m, &f, ImportPolicy::Structural);
    f.blocks[0].body.insert(
        0,
        node(
            Inst::Br {
                target: BlockId::new(0),
                args: vec![v(1), v(2)],
            },
            &[],
        ),
    );
    run(&m, &f, ImportPolicy::Refuse);
}
#[test]
fn noncanonical_declared_places_use_set_membership_without_order_or_duplicate_strengthening() {
    let (m, mut f) = fixture(vec![node(load(1), &[]), node(load(2), &[])]);
    f.summary.as_mut().unwrap().effects =
        Some(EffectSummary::pure().reading(EffectSet::Places(vec![p(1), p(0), p(1)])));
    assert!(run(&m, &f, ImportPolicy::Structural).0.is_empty());
    f.summary.as_mut().unwrap().effects.as_mut().unwrap().reads = EffectSet::Places(vec![]);
    assert_eq!(run(&m, &f, ImportPolicy::Structural).0.len(), 2);
}
#[test]
fn all_atomic_reference_counting_copy_and_frame_memory_halves_match_the_whole_oracle() {
    let (m, f) = fixture(vec![
        node(Inst::Retain { ptr: v(1) }, &[]),
        node(Inst::Release { ptr: v(2) }, &[]),
        node(
            Inst::MemCopy {
                dst: v(2),
                src: v(1),
                bytes: v(9),
                overlap: true,
            },
            &[],
        ),
        node(
            Inst::CoroSuspend {
                frame: v(1),
                state_slot: 1,
                next_state: 2,
                value: v(9),
            },
            &[],
        ),
    ]);
    let out = run(&m, &f, ImportPolicy::Structural).0;
    assert_eq!(out.len(), 5);
    assert!(
        matches!(&out[4],ValidationError::EffectSummaryViolated {effect:"frees",inst,..} if inst=="release")
    );
}
