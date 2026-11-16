// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reuse this executable's scoped allocator for actual observed type collection.
use super::{black_box, measured};
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{BinOp, CastOp, ICmpOp, UnOp};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, InterpretOptions,
    ObservedSession, ObservedValueError,
};
use trust_ir::level::NoExt;
use trust_ir::{FuncId, Inst, TensorMapNode, Ty, ValueId};

struct Observer {
    events: [Option<ExecutionProgress>; 128],
    len: usize,
    stop_at: Option<usize>,
}

impl Observer {
    fn new(stop_at: Option<usize>) -> Self {
        Self {
            events: [None; 128],
            len: 0,
            stop_at,
        }
    }
}

impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        let slot = self.events.get_mut(self.len).ok_or("test event bound")?;
        *slot = Some(event);
        self.len += 1;
        if self.stop_at == Some(self.len) {
            Err("tensor type stop")
        } else {
            Ok(())
        }
    }
}

struct Outcome<'a> {
    result: Result<Vec<&'a Ty>, ObservedValueError>,
    observer: Observer,
    cause: Option<&'static str>,
    unchanged_fuel: bool,
}

fn observed(instruction: &Inst, stop_at: Option<usize>) -> (Outcome<'_>, usize) {
    measured(|| {
        let mut observer = Observer::new(stop_at);
        let (result, cause, unchanged_fuel) = {
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let result = instruction
                .inline_types_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)));
            (
                result,
                session.first_refusal().map(|refusal| refusal.cause),
                session.remaining_fuel() == InterpretOptions::default().fuel,
            )
        };
        Outcome {
            result,
            observer,
            cause,
            unchanged_fuel,
        }
    })
}

fn cast_map() -> Inst {
    Inst::TensorMap {
        ty: Ty::Tensor(Box::new(Ty::U64), 1),
        args: vec![ValueId::new(0)],
        body: vec![TensorMapNode::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U32,
            dst_ty: Ty::U64,
            operand: 0,
        }],
    }
}

fn three_type_control() -> Inst {
    let mut operation = DialectInst::new("allocation", "control");
    operation.result_tys = vec![Ty::Tensor(Box::new(Ty::U64), 1), Ty::U32, Ty::U64];
    Inst::DialectOp(Box::new(operation))
}

#[test]
fn every_tensor_node_type_iterator_borrows_fields_without_allocating() {
    let nodes: [TensorMapNode<NoExt>; 6] = [
        TensorMapNode::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: 0,
            rhs: 1,
        },
        TensorMapNode::UnOp {
            op: UnOp::Not,
            ty: Ty::U32,
            operand: 0,
        },
        TensorMapNode::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U32,
            lhs: 0,
            rhs: 1,
        },
        TensorMapNode::Select {
            ty: Ty::U32,
            cond: 0,
            then_lane: 1,
            else_lane: 2,
        },
        TensorMapNode::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U32,
            dst_ty: Ty::U64,
            operand: 0,
        },
        TensorMapNode::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::U32,
            dst_ty: Ty::U32,
            operand: 0,
        },
    ];
    for node in nodes {
        let expected = node.types();
        let (count, allocations) = measured(|| {
            let mut count = 0;
            for actual in black_box(&node).iter_types() {
                assert!(core::ptr::eq(actual, expected[count]));
                count += 1;
            }
            count
        });
        assert_eq!(count, expected.len());
        assert_eq!(allocations, 0);
        if expected.len() == 2 {
            assert!(!core::ptr::eq(expected[0], expected[1]));
        }
    }
}

#[test]
fn observed_tensor_cast_has_only_the_same_output_allocations_as_three_borrowed_types() {
    let control = three_type_control();
    let tensor = cast_map();
    let (control, output_allocations) = observed(&control, None);
    let (actual, allocations) = observed(&tensor, None);
    assert_eq!(control.result.unwrap().len(), 3);
    let types = actual.result.unwrap();
    let Inst::TensorMap { ty, body, .. } = &tensor else {
        unreachable!()
    };
    let TensorMapNode::Cast { src_ty, dst_ty, .. } = &body[0] else {
        unreachable!()
    };
    for (actual, expected) in types.iter().zip([ty, src_ty, dst_ty]) {
        assert!(core::ptr::eq(*actual, expected));
    }
    assert_eq!(types.len(), 3);
    assert!(
        output_allocations > 0,
        "the scoped allocator must observe real output storage"
    );
    assert_eq!(
        allocations, output_allocations,
        "no temporary node-type vector"
    );
    assert!(actual.unchanged_fuel && control.unchanged_fuel);
    assert_eq!(actual.cause, None);
}

#[test]
fn every_observed_tensor_cast_stop_owns_only_admitted_output_storage() {
    let tensor = cast_map();
    let control = three_type_control();
    let (_, output_allocations) = observed(&control, None);
    let (baseline, _) = observed(&tensor, None);
    assert_eq!(baseline.result.unwrap().len(), 3);
    for stop in 1..=baseline.observer.len {
        let (actual, allocations) = observed(&tensor, Some(stop));
        assert!(
            matches!(actual.result, Err(ObservedValueError::AdmissionRefused)),
            "cut {stop}"
        );
        assert_eq!(actual.cause, Some("tensor type stop"));
        assert!(actual.unchanged_fuel);
        assert!(
            allocations <= output_allocations,
            "cut {stop}: no abandoned temporary storage"
        );
        assert!(
            actual.observer.events[stop..actual.observer.len]
                .iter()
                .all(|event| event.unwrap().phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
