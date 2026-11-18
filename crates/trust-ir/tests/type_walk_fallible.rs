// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded consumer traversal: exact order/depth and immediate refusal without
//! scanning or allocating a list of the remaining roots or tuple children.

use core::ops::ControlFlow;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use trust_ir::inst::{BindingFrameDef, BindingSlot};
use trust_ir::value::BindingFrameId;
use trust_ir::{
    AttrValue, CastOp, DialectInst, FuncId, Inst, InstG, TensorMapNode, Ty, TyG, TypeOccurrence,
    ValueId,
};

// This integration-test executable alone counts allocations, and only on the
// thread executing an explicit measurement scope. Other tests/threads cannot
// add noise; const TLS initialization itself needs no heap allocation.
thread_local! {
    static ALLOCATIONS: Cell<Option<usize>> = const { Cell::new(None) };
}

struct ScopedAllocator;

fn record_allocation() {
    let _ = ALLOCATIONS.try_with(|count| {
        if let Some(value) = count.get() {
            count.set(Some(value + 1));
        }
    });
}

unsafe impl GlobalAlloc for ScopedAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record_allocation();
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record_allocation();
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        record_allocation();
        unsafe { System.realloc(pointer, layout, size) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: ScopedAllocator = ScopedAllocator;

fn measured<T>(operation: impl FnOnce() -> T) -> (T, usize) {
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            ALLOCATIONS.with(|count| count.set(None));
        }
    }
    ALLOCATIONS.with(|count| {
        assert_eq!(count.get(), None, "allocation measurements do not nest");
        count.set(Some(0));
    });
    let reset = Reset;
    let result = operation();
    let count = ALLOCATIONS.with(|count| count.get().expect("measurement active"));
    drop(reset);
    (result, count)
}

#[test]
fn inline_preorder_depth_and_retained_borrows_match_the_infallible_api() {
    let ty = Ty::Tuple(vec![
        Ty::Ref(Box::new(Ty::Tuple(vec![
            Ty::FnItem(FuncId::new(7)),
            Ty::I8,
        ]))),
        Ty::I32,
    ]);
    let original = ty.clone();
    let mut old = Vec::new();
    ty.visit_types(|ty| old.push(ty));
    let mut seen = Vec::new();
    let mut depths = Vec::new();
    assert_eq!(
        ty.try_visit_types(|ty, depth| {
            seen.push(ty);
            depths.push(depth);
            ControlFlow::<()>::Continue(())
        }),
        ControlFlow::Continue(())
    );
    assert_eq!(seen, old);
    assert_eq!(depths, [0, 1, 2, 3, 3, 1]);
    assert_eq!(seen[3], &Ty::FnItem(FuncId::new(7)));
    assert_eq!(ty, original);
}

#[test]
fn deep_and_wide_inline_inputs_stop_at_the_requested_node_without_bulk_scratch() {
    let mut ty = Ty::FnItem(FuncId::new(7));
    for _ in 0..100_000 {
        ty = Ty::Ref(Box::new(ty));
    }
    let mut count = 0;
    let (result, allocations) = measured(|| {
        ty.try_visit_types(|_, depth| {
            count += 1;
            if depth == 128 {
                ControlFlow::Break(depth)
            } else {
                ControlFlow::Continue(())
            }
        })
    });
    assert_eq!(result, ControlFlow::Break(128));
    assert_eq!(count, 129);
    assert_eq!(allocations, 0, "a unary chain needs no sibling scratch");
    let mut last_depth = 0;
    assert_eq!(
        ty.try_visit_types(|_, depth| {
            last_depth = depth;
            ControlFlow::<()>::Continue(())
        }),
        ControlFlow::Continue(())
    );
    assert_eq!(last_depth, 100_000);
    // Recursive destruction is not part of this traversal contract.
    while let Ty::Ref(inner) = ty {
        ty = *inner;
    }

    let wide = Ty::Tuple(vec![Ty::I8; 100_000]);
    let (result, allocations) =
        measured(|| wide.try_visit_types(|_, _| ControlFlow::Break("root")));
    assert_eq!(result, ControlFlow::Break("root"));
    assert_eq!(
        allocations, 0,
        "refusing the root must not inspect/push its children"
    );
    let mut count = 0;
    let (result, allocations) = measured(|| {
        wide.try_visit_types(|_, depth| {
            count += 1;
            if depth == 1 {
                ControlFlow::Break("child")
            } else {
                ControlFlow::Continue(())
            }
        })
    });
    assert_eq!(result, ControlFlow::Break("child"));
    assert_eq!(count, 2);
    assert!(
        allocations <= 1,
        "one borrowed sibling iterator, never one item per child"
    );
    assert!(matches!(&wide, Ty::Tuple(fields) if fields.len() == 100_000));
}

fn occurrence_key(occurrence: TypeOccurrence<'_, u8>) -> (bool, String) {
    match occurrence {
        TypeOccurrence::Spelled(ty) => (true, format!("{ty:?}")),
        TypeOccurrence::Ground(ty) => (false, format!("{ty:?}")),
    }
}

#[test]
fn generic_spelled_and_ground_roots_keep_field_order_and_original_inputs() {
    let cast: InstG<u8> = InstG::Cast {
        op: CastOp::Bitcast,
        src_ty: TyG::Tuple(vec![TyG::Ext(4), TyG::FnItem(FuncId::new(7))]),
        dst_ty: TyG::Ref(Box::new(TyG::I16)),
        operand: ValueId::new(0),
    };
    let frame: InstG<u8> = InstG::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(0),
            "frame",
            vec![
                BindingSlot::new("first", Ty::Tuple(vec![Ty::I8, Ty::Bool])),
                BindingSlot::new("second", Ty::I32),
            ],
        ),
    };
    let dialect: InstG<u8> = InstG::DialectOp(Box::new(
        DialectInst::new("test", "typed")
            .with_result_tys([Ty::I64, Ty::Ref(Box::new(Ty::Bool))])
            .with_attr("untyped", AttrValue::Bool(true))
            .with_attr("type", AttrValue::Ty(Ty::U8)),
    ));
    let expected_depths = [vec![0, 1, 1, 0, 1], vec![0, 1, 1, 0], vec![0, 0, 1, 0]];
    for ((inst, expected), expected_spelled) in [cast, frame, dialect]
        .into_iter()
        .zip(expected_depths)
        .zip([true, false, false])
    {
        let original = inst.clone();
        let mut old_roots = Vec::new();
        inst.visit_type_root_occurrences(|ty| old_roots.push(occurrence_key(ty)));
        let mut roots = Vec::new();
        assert_eq!(
            inst.try_visit_type_root_occurrences(|ty| {
                roots.push(occurrence_key(ty));
                ControlFlow::<()>::Continue(())
            }),
            ControlFlow::Continue(())
        );
        assert_eq!(roots, old_roots);
        let mut old = Vec::new();
        inst.visit_type_occurrences(|ty| old.push(occurrence_key(ty)));
        let mut full = Vec::new();
        let mut depths = Vec::new();
        assert_eq!(
            inst.try_visit_type_occurrences(|ty, depth| {
                full.push(occurrence_key(ty));
                depths.push(depth);
                ControlFlow::<()>::Continue(())
            }),
            ControlFlow::Continue(())
        );
        assert_eq!(full, old);
        assert_eq!(depths, expected);
        assert_eq!(inst, original);
        assert_eq!(
            roots
                .iter()
                .map(|(spelled, _)| *spelled)
                .collect::<Vec<_>>(),
            vec![expected_spelled; roots.len()]
        );
    }
}

#[test]
fn high_arity_instruction_refusal_does_not_allocate_or_scan_a_root_list() {
    let tensor: Inst = Inst::TensorMap {
        ty: Ty::Tensor(Box::new(Ty::I32), 1),
        args: vec![],
        body: vec![
            TensorMapNode::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I32,
                dst_ty: Ty::U32,
                operand: 0,
            };
            100_000
        ],
    };
    let frame = Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(0),
            "wide",
            vec![BindingSlot::new("", Ty::I8); 100_000],
        ),
    };
    let dialect = Inst::DialectOp(Box::new(
        DialectInst::new("test", "wide")
            .with_result_tys(vec![Ty::I8; 100_000])
            .with_attr("later", AttrValue::Ty(Ty::Bool)),
    ));
    for inst in [tensor, frame, dialect] {
        let mut count = 0;
        let (result, allocations) = measured(|| {
            inst.try_visit_type_roots(|_| {
                count += 1;
                ControlFlow::Break("budget")
            })
        });
        assert_eq!(result, ControlFlow::Break("budget"));
        assert_eq!(count, 1);
        assert_eq!(
            allocations, 0,
            "no eager root or TensorMap node type vectors"
        );
        let (result, allocations) =
            measured(|| inst.try_visit_types(|_, _| ControlFlow::Break("budget")));
        assert_eq!(result, ControlFlow::Break("budget"));
        assert_eq!(allocations, 0);
    }
}

#[test]
fn tensor_root_order_and_break_between_cast_fields_are_exact() {
    let inst: Inst = Inst::TensorMap {
        ty: Ty::Tensor(Box::new(Ty::I32), 1),
        args: vec![],
        body: vec![
            TensorMapNode::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I16,
                dst_ty: Ty::U16,
                operand: 0,
            },
            TensorMapNode::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I64,
                dst_ty: Ty::U64,
                operand: 0,
            },
        ],
    };
    let original = inst.clone();
    let mut roots = Vec::new();
    inst.visit_type_roots(|ty| roots.push(ty.clone()));
    assert_eq!(
        roots,
        [
            Ty::Tensor(Box::new(Ty::I32), 1),
            Ty::I16,
            Ty::U16,
            Ty::I64,
            Ty::U64
        ]
    );
    let mut seen = Vec::new();
    assert_eq!(
        inst.try_visit_type_roots(|ty| {
            seen.push(ty.clone());
            if *ty == Ty::I16 {
                ControlFlow::Break(7)
            } else {
                ControlFlow::Continue(())
            }
        }),
        ControlFlow::Break(7)
    );
    assert_eq!(seen, roots[..2]);
    assert_eq!(inst, original);
    let mut called = false;
    assert_eq!(
        Inst::NullPtr.try_visit_types(|_, _| {
            called = true;
            ControlFlow::<()>::Continue(())
        }),
        ControlFlow::Continue(())
    );
    assert!(!called);
}
