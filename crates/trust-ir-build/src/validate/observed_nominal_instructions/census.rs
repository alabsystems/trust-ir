// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn census<O: ExecutionObserver>(
        &mut self,
        node: &InstrNode,
        values: &ObservedValueTypes,
        nominal: &ObservedNominalTypeReachability<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<(bool, bool)> {
        let mut dialect = nominal.contains_dialect_instruction_types_observed(
            &node.inst,
            work.session,
            work.site,
        )?;
        let mut handle = nominal.contains_handle_instruction_types_observed(
            &node.inst,
            work.session,
            work.site,
        )?;
        let mut at = 0;
        while let Some(value) = work.at(&node.results, at)? {
            work.admit(1, size_of::<ValueId>())?;
            let value = *value;
            Self::note(value, values, nominal, &mut dialect, &mut handle, work)?;
            work.next(&mut at)?;
        }
        // Full actual child is owned before any next fallible operation.
        self.operands = node.inst.value_operands_observed(work.session, work.site)?;
        let mut at = 0;
        while let Some(value) = work.at(&self.operands, at)? {
            work.admit(1, size_of::<ValueId>())?;
            let value = *value;
            Self::note(value, values, nominal, &mut dialect, &mut handle, work)?;
            work.next(&mut at)?;
        }
        Ok((handle, dialect))
    }
    fn note<O: ExecutionObserver>(
        value: ValueId,
        values: &ObservedValueTypes,
        nominal: &ObservedNominalTypeReachability<'_>,
        dialect: &mut bool,
        handle: &mut bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some(ty) = values.get_observed(value, work.session, work.site)? {
            let d = nominal.contains_dialect_observed(ty, work.session, work.site)?;
            work.admit(1, size_of::<bool>())?;
            *dialect |= d;
            let h = nominal.contains_handle_observed(ty, work.session, work.site)?;
            work.admit(1, size_of::<bool>())?;
            *handle |= h;
        }
        Ok(())
    }
}
pub(super) fn exact<O: ExecutionObserver>(
    value: ValueId,
    expected: &Ty,
    values: &ObservedValueTypes,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    match values.get_observed(value, work.session, work.site)? {
        Some(actual) => actual.structural_eq_observed(expected, work.session, work.site),
        None => Ok(false),
    }
}
pub(super) fn exact_function<O: ExecutionObserver>(
    callee: ValueId,
    sig: trust_ir::value::FuncTyId,
    values: &ObservedValueTypes,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let actual = values.get_observed(callee, work.session, work.site)?;
    work.admit(1, size_of::<bool>())?;
    Ok(matches!(actual,Some(Ty::Func(actual)) if *actual==sig))
}
