// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Outer closure IDs from the same actual module result plan, no cloned types.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::value::ClosureTyId;
/// Diagnostic data only: preserve every actual result ordinal, including
/// ordinals with no attached SSA value. The original Pure rule only matches
/// outer Closure; no nested type or representation is reinterpreted here.
pub(in crate::validate) fn module_closure_results_observed<O: ExecutionObserver>(
    module: &Module,
    node: &trust_ir::InstrNode,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<(usize, ClosureTyId)>> {
    let mut work = Work { session, site };
    work.admit(
        1,
        size_of::<Vec<(usize, ClosureTyId)>>()
            + size_of::<Option<plan::Plan<'_>>>()
            + size_of::<Work<'_, '_, O>>(),
    )?;
    let mut rows = Vec::new();
    let mut pending_plan = None;
    let result = (|| {
        // Same finite instruction dispatch fee as the actual module value map.
        work.admit(67, 4 * size_of::<plan::Plan<'_>>())?;
        pending_plan = Some(plan::for_instruction(
            &node.inst,
            Context::Module(module),
            &mut work,
        )?);
        let plan = pending_plan.ok_or(ObservedValueError::InvalidRange)?;
        work.admit(4, size_of::<usize>())?;
        let len = match plan {
            plan::Plan::One(_) => 1,
            plan::Plan::Pair(_, _) => 2,
            plan::Plan::Types(types) => types.len(),
            plan::Plan::Empty => 0,
            // Module context never repeats a single type for unlimited SSA
            // results. A future plan change must acquire an exact finite rule.
            plan::Plan::All(_) => return Err(ObservedValueError::InvalidRange),
        };
        let mut index = 0;
        loop {
            work.admit(1, size_of::<bool>())?;
            if index == len {
                break;
            }
            let atom = plan
                .at(index, &mut work)?
                .ok_or(ObservedValueError::InvalidRange)?;
            work.admit(2, size_of::<Option<ClosureTyId>>())?;
            if let plan::Atom::Borrowed(Ty::Closure(id)) = atom {
                work.reserve(&mut rows)?;
                work.admit(1, size_of::<(usize, ClosureTyId)>())?;
                rows.push((index, *id));
            }
            work.admit(1, size_of::<usize>())?;
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        Ok(())
    })();
    work.retire(pending_plan.take());
    let result = result.and_then(|()| work.publication(size_of::<Vec<(usize, ClosureTyId)>>()));
    match result {
        Ok(()) => Ok(rows),
        Err(error) => {
            loop {
                work.session.retirement_step(
                    site,
                    size_of::<Option<(usize, ClosureTyId)>>().saturating_add(1),
                );
                if rows.pop().is_none() {
                    break;
                }
            }
            work.retire(rows);
            Err(work.terminal(error))
        }
    }
}
