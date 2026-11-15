// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored controls; no execution evidence.
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, TyId};
use trust_ir::{Block, CallingConv, FatPtrKind, InstrNode};
mod catalog;
mod parity;
mod stops;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}

impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(progress);
        if self.stop == Some(self.events.len()) {
            return Err("original value stop");
        }
        self.work = self.work.checked_add(progress.work).ok_or("overflow")?;
        self.bytes = self
            .bytes
            .checked_add(progress.copy_bytes)
            .ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(71))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn b(id: u32) -> BlockId {
    BlockId::new(id)
}

fn function(nodes: Vec<InstrNode>) -> Function {
    let mut f = Function::new(FuncId::new(71), "types", FuncTyId::new(0), b(0));
    let mut block = Block::new(b(0));
    block.body = nodes;
    f.blocks.push(block);
    f
}

fn node(inst: Inst, values: &[u32]) -> InstrNode {
    InstrNode::new(inst).with_results(values.iter().copied().map(v))
}

fn run(f: &Function, module: Option<&Module>) -> (ObservedValueTypes, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = match module {
        Some(module) => build_module_value_types_observed(f, module, &mut session, site()),
        None => build_function_value_types_observed(f, &mut session, site()),
    }
    .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (result, observer)
}

fn parity(f: &Function, module: Option<&Module>) -> BTreeMap<u32, Ty> {
    let expected = match module {
        Some(module) => super::super::build_module_value_types(f, module),
        None => super::super::build_function_value_types(f),
    };
    let (actual, observer) = run(f, module);
    let actual: BTreeMap<_, _> = actual.rows.into_iter().collect();
    assert_eq!(actual, expected);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}

fn fixture() -> Function {
    let mut f = function(vec![
        node(Inst::Borrow { ptr: v(8) }, &[7]),
        node(Inst::BorrowMut { ptr: v(9) }, &[8]),
        node(
            Inst::Copy {
                ty: Ty::Tuple(vec![Ty::U32, Ty::Ptr]),
                operand: v(0),
            },
            &[1, 2],
        ),
        node(
            Inst::Overflow {
                op: trust_ir::OverflowOp::AddOverflow,
                ty: Ty::I64,
                lhs: v(1),
                rhs: v(2),
            },
            &[3, 4, 5],
        ),
        node(
            Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty: Ty::Vector(Box::new(Ty::U32), 8),
                lhs: v(1),
                rhs: v(2),
            },
            &[6],
        ),
    ]);
    let mut tail = Block::new(b(5));
    tail.params
        .push((v(9), Ty::FatPtr(FatPtrKind::Slice(TyId::new(0)))));
    f.blocks.push(tail);
    f
}
