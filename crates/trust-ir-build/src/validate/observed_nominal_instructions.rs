// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original handle-first / dialect-intersection instruction rule, actual work.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_handle_aggregate::handle_aggregate_lane_rule_observed;
use super::observed_handle_enum_guards::ObservedHandleEnumGuards;
use super::observed_sealed_slots::{ObservedSealedHandleSlots, handle_slot_rule_observed};
use super::*;
use core::mem::{size_of, take};
use trust_ir::InstrNode;
use trust_ir::ObservedNominalTypeReachability;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod census;
mod dialect;
mod handles;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    operands: Vec<ValueId>,
    location: String,
    detail: String,
    errors: Vec<ValidationError>,
}
#[derive(Clone, Copy)]
enum Family {
    Handle,
    Dialect,
}
#[derive(Clone, Copy)]
enum Decision {
    Allowed,
    GenericRefusal,
    DetailedRefusal,
}
/// Full original single-instruction rule, not signature/edge/SSA/module/source
/// authority. Actual original module, full value map, nominal summary, guards
/// and sealed-slot analysis remain the mandatory caller's identities. Missing
/// optional guard/slot means only the original conservative semantic refusal;
/// operational child stops are typed outer Err and never missing data.
///
/// Both original inline queries, every actual result and every actual operand
/// are visited even after either family bit is true. Handle checks run first;
/// success still falls through to dialect checks when both families occur.
/// Every full owned child/partial diagnostic and prior output stays held until
/// complete transfer or original-session draining. No owner/grant/deadline/TLS/
/// fuel/authority is introduced. Full module adoption and physical bounds OPEN.
pub(super) fn validate_nominal_instruction_types_observed<O: ExecutionObserver>(
    module: &Module,
    node: &InstrNode,
    values: &ObservedValueTypes,
    nominal: &ObservedNominalTypeReachability<'_>,
    block: BlockId,
    index: usize,
    guards: Option<&ObservedHandleEnumGuards<'_>>,
    slots: Option<&ObservedSealedHandleSlots<'_>>,
    location: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(
        module, node, values, nominal, block, index, guards, slots, location, &mut work,
    );
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        node: &InstrNode,
        values: &ObservedValueTypes,
        nominal: &ObservedNominalTypeReachability<'_>,
        block: BlockId,
        index: usize,
        guards: Option<&ObservedHandleEnumGuards<'_>>,
        slots: Option<&ObservedSealedHandleSlots<'_>>,
        location: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let (has_handle, has_dialect) = self.census(node, values, nominal, work)?;
        work.admit(2, 2 * size_of::<bool>())?;
        if !has_handle && !has_dialect {
            return Ok(());
        }
        if has_handle {
            let decision = self.handles(
                module, node, values, nominal, block, index, guards, slots, work,
            )?;
            work.admit(1, size_of::<Decision>())?;
            match decision {
                Decision::Allowed => {}
                Decision::DetailedRefusal => return self.error(Family::Handle, location, work),
                Decision::GenericRefusal => {
                    work.admit(1, size_of::<trust_ir::inst::InstShape>())?;
                    work.text("`", &mut self.detail)?;
                    work.text(node.inst.shape().name(), &mut self.detail)?;
                    work.text("` cannot produce, consume or reinterpret an opaque runtime handle; a handle may only be copied, selected, passed to or returned from an exact-typed call, carried across a branch edge, built and projected as an exact-typed struct / tuple / enum lane, or spilled to a sealed stack slot",&mut self.detail)?;
                    return self.error(Family::Handle, location, work);
                }
            }
            work.admit(1, size_of::<bool>())?;
            if !has_dialect {
                return Ok(());
            }
        }
        let decision = self.dialect(module, &node.inst, values, nominal, work)?;
        work.admit(1, size_of::<Decision>())?;
        match decision {
            Decision::Allowed => Ok(()),
            Decision::DetailedRefusal => self.error(Family::Dialect, location, work),
            Decision::GenericRefusal => {
                work.text("nominal dialect values require exact-typed transport or an explicit dialect operation; scalar, cast, and memory use requires legalization",&mut self.detail)?;
                self.error(Family::Dialect, location, work)
            }
        }
    }
    fn error<O: ExecutionObserver>(
        &mut self,
        family: Family,
        location: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(location, &mut self.location)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        let location = take(&mut self.location);
        let detail = take(&mut self.detail);
        self.errors.push(match family {
            Family::Handle => ValidationError::InvalidHandleUse { location, detail },
            Family::Dialect => ValidationError::InvalidDialectType { location, detail },
        });
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.rows(take(&mut self.operands));
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.detail));
    }
}
