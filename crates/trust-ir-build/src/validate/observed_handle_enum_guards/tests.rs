// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: actual ordinary guard and actual observed dominators.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::Block;
use trust_ir::inst::SwitchCase;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::FuncTyId;
mod custody;
mod parity;
mod stops;
type Ordinary = super::super::HandleEnumGuards;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    work: Rc<Cell<usize>>,
    bytes: Rc<Cell<usize>>,
    stop: Option<usize>,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup_after: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original guard stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        self.work
            .set(self.work.get().checked_add(e.work).ok_or("overflow")?);
        self.bytes.set(
            self.bytes
                .get()
                .checked_add(e.copy_bytes)
                .ok_or("overflow")?,
        );
        if self.work_cap.is_some_and(|n| self.work.get() > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes.get() > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1089))
}
fn tag(aggregate: u32, result: Option<u32>) -> InstrNode {
    let n = InstrNode::new(Inst::ExtractField {
        aggregate: ValueId::new(aggregate),
        ty: Ty::Enum(trust_ir::value::EnumId::new(7)),
        field: 0,
    });
    if let Some(result) = result {
        n.with_result(ValueId::new(result))
    } else {
        n
    }
}
fn graph(targets: &[Vec<usize>]) -> Function {
    let ids = [u32::MAX, 17, 4_000_000_000, 99, 111];
    let mut f = Function::new(
        FuncId::new(1089),
        "guards",
        FuncTyId::new(0),
        BlockId::new(ids[0]),
    );
    for (i, dests) in targets.iter().enumerate() {
        let mut b = Block::new(BlockId::new(ids[i]));
        b.body.push(tag(55, Some(7)));
        b.body.push(InstrNode::new(
            if let Some((default, cases)) = dests.split_last() {
                Inst::Switch {
                    value: ValueId::new(7),
                    default: BlockId::new(ids[*default]),
                    default_args: vec![],
                    exhaustive_enum_unreachable: false,
                    cases: cases
                        .iter()
                        .enumerate()
                        .map(|(index, target)| SwitchCase {
                            value: Constant::Int(index as i128),
                            target: BlockId::new(ids[*target]),
                            args: vec![],
                        })
                        .collect(),
                }
            } else {
                Inst::Return { values: vec![] }
            },
        ));
        f.blocks.push(b);
    }
    f
}
fn fixture() -> Function {
    graph(&[vec![1, 2], vec![3], vec![3], vec![]])
}
fn selected<O: ExecutionObserver>(
    g: &ObservedHandleEnumGuards<'_>,
    b: BlockId,
    aggregate: u32,
    ds: &[i128],
    s: &mut ObservedSession<'_, O>,
) -> Vec<usize> {
    let out = g
        .variants_selected_at_observed(b, aggregate, ds, s, site())
        .unwrap();
    let copy = out.clone(); // Test-owned scalar oracle, not part of production.
    retire_selected_variants_observed(out, s, site()).unwrap();
    copy
}
fn parity(f: &Function) -> Observer {
    let old = Ordinary::new(f);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        ObservedHandleEnumGuards::function_reads_a_non_tag_lane_observed(f, &mut s, site())
            .unwrap(),
        Ordinary::function_reads_a_non_tag_lane(f)
    );
    let g = ObservedHandleEnumGuards::new_observed(f, &mut s, site()).unwrap();
    assert_eq!(g.edges, old.edges);
    for b in f.blocks.iter().map(|b| b.id).chain([BlockId::new(888)]) {
        for aggregate in [0, 55, 66, u32::MAX] {
            for ds in [
                &[][..],
                &[0, 1, -1][..],
                &[0, 0, 1][..],
                &[i128::MIN, i128::MAX][..],
            ] {
                assert_eq!(
                    selected(&g, b, aggregate, ds, &mut s),
                    old.variants_selected_at(b, aggregate, ds)
                );
            }
        }
    }
    g.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    o
}
fn query_trace(f: &Function) -> (Observer, usize, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let g = ObservedHandleEnumGuards::new_observed(f, &mut s, site()).unwrap();
    let begin = calls.get();
    let out = g
        .variants_selected_at_observed(f.blocks[1].id, 55, &[0, 1, 2], &mut s, site())
        .unwrap();
    assert_eq!(out, vec![0]);
    let end = calls.get();
    retire_selected_variants_observed(out, &mut s, site()).unwrap();
    g.retire_observed(&mut s, site()).unwrap();
    drop(s);
    (o, begin, end)
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire(work);
}
fn empty(state: &State) -> bool {
    state.tree.is_none() && state.tags.capacity() == 0 && state.edges.capacity() == 0
}
