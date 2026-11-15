// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original sealed-slot construction, use scan and access rules.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::handle_slots::SEALED;
use super::observed_handle_slot_shape::slot_shape_observed;
use super::observed_value_types::ObservedValueTypes;
use super::*;
use core::mem::{size_of, take};
use trust_ir::analysis::DominatorTree;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod allocations;
mod borrows;
mod census;
mod cost;
mod definitions;
mod dominance;
mod queries;
mod retirement;
mod rule;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
mod unseal;
pub(super) use rule::handle_slot_rule_observed;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
type Point = (BlockId, usize);
struct Slot {
    ty: Ty,
    site: Point,
    natural_align: Option<u64>,
    unsealed: Option<String>,
    stores: Vec<Point>,
}
/// Actual immutable function's fully observed analysis data, never a capability.
/// The original full module caller preserves handle census + present nominal
/// summary + observed allocation predicate. This is DATA, never source, module,
/// SSA, heap/handle origin, proof or runtime authority. Every actual child and
/// owning pending/old value remains held across the next fallible step. No
/// operational refusal becomes an empty or missing successful analysis.
pub(super) struct ObservedSealedHandleSlots<'f> {
    _function: &'f Function,
    dominators: DominatorTree,
    slots: BTreeMap<u32, Slot>,
    members: BTreeMap<u32, (u32, Point)>,
}
#[derive(Default)]
struct State {
    dominators: Option<DominatorTree>,
    definitions: BTreeMap<u32, usize>,
    slots: BTreeMap<u32, Slot>,
    members: BTreeMap<u32, (u32, Point)>,
    multiply_defined: Vec<(u32, u32)>,
    operands: Vec<ValueId>,
    unsealing: Vec<(u32, String)>,
    pending_type: Option<Ty>,
    pending_slot: Option<Slot>,
    old_slot: Option<Slot>,
    pending_unsealed: Option<String>,
    pending_natural: Option<u64>,
    reason: String,
    render: String,
}

impl<'f> ObservedSealedHandleSlots<'f> {
    pub(super) fn function_allocates_a_handle_observed<O: ExecutionObserver>(
        function: &Function,
        nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<bool>() + size_of::<Work<'_, '_, O>>())?;
        let result: R<bool> = (|| {
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    work.admit(1, size_of::<&Inst>())?;
                    if let Inst::Alloca { ty, .. } = &node.inst
                        && nominal.contains_handle_observed(ty, work.session, work.site)?
                    {
                        return Ok(true);
                    }
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            Ok(false)
        })();
        match result.and_then(|answer| {
            work.publication(size_of::<bool>())?;
            Ok(answer)
        }) {
            Ok(answer) => Ok(answer),
            Err(error) => Err(work.terminal(error)),
        }
    }
    pub(super) fn new_observed<O: ExecutionObserver>(
        layouts: &trust_ir::LayoutTable<'_>,
        function: &'f Function,
        nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.build(layouts, function, nominal, &mut work);
        state.retire_scratch(&mut work);
        if let Err(error) = result.and_then(|()| work.admit(1, size_of::<Self>())) {
            state.retire_analysis(&mut work);
            return Err(work.terminal(error));
        }
        let Some(dominators) = state.dominators.take() else {
            state.retire_analysis(&mut work);
            return Err(work.terminal(ObservedValueError::InvalidRange));
        };
        let output = Self {
            _function: function,
            dominators,
            slots: take(&mut state.slots),
            members: take(&mut state.members),
        };
        if let Err(error) = work.publication(size_of::<Self>()) {
            output.retire_inner(&mut work);
            return Err(work.terminal(error));
        }
        Ok(output)
    }
    pub(super) fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        self.retire_inner(&mut work);
        work.publication(0)
    }
    fn retire_inner<O: ExecutionObserver>(self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Self>() + size_of::<State>() + 1);
        let Self {
            _function: _,
            dominators,
            slots,
            members,
        } = self;
        let mut state = State {
            dominators: Some(dominators),
            slots,
            members,
            ..State::default()
        };
        state.retire_analysis(work);
    }
}
impl State {
    fn build<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'_>,
        function: &Function,
        nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Exact original constructor group order, no counted prewalk substitute.
        self.dominators = Some(DominatorTree::new_observed(
            function,
            work.session,
            work.site,
        )?);
        self.definitions(function, work)?;
        self.allocations(layouts, function, nominal, work)?;
        self.borrows(function, work)?;
        self.multiply_defined(work)?;
        self.scan_uses(function, work)
    }
}
