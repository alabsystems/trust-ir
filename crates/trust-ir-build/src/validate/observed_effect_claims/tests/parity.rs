// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn all67_instruction_routes_and_all_four_claim_modes_match_the_original() {
    let inventory = witnesses::all();
    assert_eq!(inventory.len(), 67);
    let names: std::collections::BTreeSet<_> = inventory.iter().map(names::mnemonic).collect();
    assert_eq!(names.len(), 67);
    for instruction in &inventory {
        assert_eq!(
            names::mnemonic(instruction),
            super::super::super::instruction_kind(instruction)
        );
        for mode in 0..4 {
            let mut f = function(vec![node(instruction.clone(), &[])]);
            f.attrs.readnone = mode & 1 != 0;
            f.attrs.readonly = mode & 2 != 0;
            parity(&f, None);
            for (readnone, readonly) in [(false, false), (false, true), (true, false), (true, true)]
            {
                let mut module = Module::new("claim-matrix");
                module
                    .functions
                    .push(callee(9, "callee", readnone, readonly));
                parity(&f, Some(&module));
            }
        }
    }
}
#[test]
fn readnone_precedence_no_claim_and_bodyless_keep_original_empty_rules() {
    let mut f = function(vec![node(load(1), &[])]);
    f.attrs.readonly = true;
    let errors = parity(&f, None);
    assert!(matches!(
        &errors[0],
        ValidationError::FuncAttrClaimViolated {
            attr: "readnone",
            ..
        }
    ));
    f.attrs.readnone = false;
    assert!(parity(&f, None).is_empty());
    f.attrs.readonly = false;
    f.name = "unread-λ".repeat(5000);
    let (_, observer) = run(&f, None);
    assert!(
        observer
            .events
            .iter()
            .all(|event| event.copy_bytes < f.name.len())
    );
    f.attrs.readnone = true;
    f.blocks.clear();
    let mut module = Module::new("bodyless");
    module.drop_glue.push(DropGlueEntry {
        ty: Ty::Tuple(vec![Ty::U32; 5000]),
        glue: FuncId::new(9),
    });
    let (errors, observer) = run(&f, Some(&module));
    assert!(errors.is_empty());
    assert!(
        !observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::DropGlueIndex)
    );
    assert!(parity(&f, Some(&module)).is_empty());
}
#[test]
fn relaxed_memory_and_all_atomic_strengths_preserve_local_exemption_only() {
    let orderings = [
        Ordering::Relaxed,
        Ordering::Acquire,
        Ordering::Release,
        Ordering::AcqRel,
        Ordering::SeqCst,
    ];
    for readonly in [false, true] {
        for local in [false, true] {
            let ptr = if local { 10 } else { 1 };
            for ordering in orderings {
                let instructions = [
                    Inst::AtomicLoad {
                        ty: Ty::U32,
                        ptr: v(ptr),
                        ordering,
                    },
                    Inst::AtomicStore {
                        ty: Ty::U32,
                        ptr: v(ptr),
                        value: v(1),
                        ordering,
                    },
                    Inst::AtomicRMW {
                        op: AtomicRMWOp::Xchg,
                        ty: Ty::U32,
                        ptr: v(ptr),
                        value: v(1),
                        ordering,
                    },
                ];
                for (kind, instruction) in instructions.into_iter().enumerate() {
                    let mut f = function(vec![node(alloca(), &[10]), node(instruction, &[])]);
                    f.attrs.readnone = !readonly;
                    f.attrs.readonly = readonly;
                    let errors = parity(&f, None);
                    let allowed = ordering == Ordering::Relaxed && (local || readonly && kind == 0);
                    assert_eq!(errors.is_empty(), allowed);
                }
                for weak in [false, true] {
                    for failure in orderings {
                        let mut f = function(vec![
                            node(alloca(), &[10]),
                            node(
                                Inst::CmpXchg {
                                    ty: Ty::U32,
                                    ptr: v(ptr),
                                    expected: v(1),
                                    desired: v(1),
                                    success: ordering,
                                    failure,
                                    weak,
                                },
                                &[],
                            ),
                        ]);
                        f.attrs.readnone = !readonly;
                        f.attrs.readonly = readonly;
                        assert_eq!(
                            parity(&f, None).is_empty(),
                            local && ordering == Ordering::Relaxed && failure == Ordering::Relaxed
                        );
                    }
                }
            }
        }
    }
}
#[test]
fn synchronizing_and_opaque_effects_never_gain_a_local_pointer_exemption() {
    let refused = [
        Inst::Fence {
            ordering: Ordering::Relaxed,
        },
        Inst::HeapAlloc {
            ty: Ty::U32,
            count: None,
            align: None,
            origin: AllocOrigin::RustHeap,
        },
        Inst::Dealloc { ptr: v(10) },
        Inst::Retain { ptr: v(10) },
        Inst::Release { ptr: v(10) },
        Inst::IsUnique { ptr: v(10) },
        Inst::MemCopy {
            dst: v(10),
            src: v(10),
            bytes: v(10),
            overlap: false,
        },
        Inst::MemSet {
            dst: v(10),
            byte: v(10),
            bytes: v(10),
        },
        dialect(0),
    ];
    for instruction in refused {
        let mut f = function(vec![node(alloca(), &[10]), node(instruction, &[])]);
        for readonly in [false, true] {
            f.attrs.readnone = !readonly;
            f.attrs.readonly = readonly;
            assert_eq!(parity(&f, None).len(), 1);
        }
    }
}
#[test]
fn coroutine_frame_is_a_write_and_volatile_reads_keep_the_original_rules() {
    for local in [false, true] {
        let ptr = if local { 10 } else { 1 };
        let f = function(vec![
            node(alloca(), &[10]),
            node(
                Inst::CoroSuspend {
                    frame: v(ptr),
                    state_slot: u32::MAX,
                    next_state: i64::MAX,
                    value: v(1),
                },
                &[],
            ),
        ]);
        assert_eq!(parity(&f, None).is_empty(), local);
        let f = function(vec![
            node(alloca(), &[10]),
            node(
                Inst::Load {
                    ty: Ty::U32,
                    ptr: v(ptr),
                    volatile: true,
                    align: None,
                },
                &[],
            ),
        ]);
        assert_eq!(parity(&f, None).is_empty(), local);
    }
}
#[test]
fn physical_blocks_and_nodes_keep_exact_diagnostic_order_and_names() {
    let mut f = function(vec![node(load(1), &[]), node(store(1), &[])]);
    f.name = "f\0λ🙂".repeat(400);
    let mut second = Block::new(BlockId::new(8));
    second.body.push(node(
        Inst::Fence {
            ordering: Ordering::Acquire,
        },
        &[],
    ));
    f.blocks.push(second);
    let errors = parity(&f, None);
    assert_eq!(errors.len(), 3);
    assert!(text(&errors[0]).starts_with("load (reads"));
    assert!(text(&errors[1]).starts_with("store (writes"));
    assert_eq!(text(&errors[2]), "fence (a fence synchronizes)");
    for (error, block_id) in errors.iter().zip([0, 0, 8]) {
        assert!(
            matches!(error,ValidationError::FuncAttrClaimViolated{function,attr:"readnone",block,..} if function==&f.name && *block==block_id)
        );
    }
}
#[test]
fn all_physical_parameters_and_every_result_are_collected_before_effects() {
    let mut f = function(vec![node(alloca(), &[10, 11, 10]), node(copy(10), &[12])]);
    f.blocks[0].params.push((v(1), Ty::Ptr));
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.run(&f, None, &mut work).unwrap();
    assert_eq!(state.definitions.len(), 6);
    assert!(matches!(state.definitions[0],(id,Definition::Parameter{block:0,index:0}) if id==v(1)));
    assert!(matches!(state.definitions[1],(id,Definition::Parameter{block:0,index:1}) if id==v(1)));
    assert_eq!(state.definitions[2].0, v(10));
    assert_eq!(state.definitions[3].0, v(11));
    assert_eq!(state.definitions[4].0, v(10));
    assert_eq!(state.definitions[5].0, v(12));
    state.retire_scratch(&mut work);
    state.retire_errors(&mut work);
    assert!(empty(&state));
}
