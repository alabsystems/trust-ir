// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! First-typeable-definition query, distinct from last-write value maps.
#![allow(
    clippy::while_let_loop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::{Function, Inst, Ty, ValueId};
use core::mem::{align_of, size_of};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod inference;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use inference::Inferred;
use scan::Definition;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Default)]
struct State {
    pending: Option<Ty>,
}

/// Return the original first typeable physical definition, resolving borrows
/// through their original instruction-count-bounded chain. This deliberately
/// does not consult a last-write-wins value map or callee signatures. All result
/// IDs of a typeable instruction share this interface's declared single type.
/// The supplied original session/site owns every scan, actual type clone and
/// refusal cleanup. No incomplete query answers None after an operational stop.
/// Successful output/input disposal and physical allocator/panic/time bounds
/// remain caller responsibilities; this query creates no typing/proof authority.
pub fn function_value_type_observed<O: ExecutionObserver>(
    function: &Function,
    value: ValueId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<Ty>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.run(function, value, &mut work);
    work.retire_fixed();
    let result = result.and_then(|()| work.publication());
    match result {
        Ok(()) => Ok(state.pending.take()),
        Err(error) => {
            state.retire(&mut work);
            Err(work.terminal(error))
        }
    }
}

impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(first) = scan::borrow_operand(function, value, work)? else {
            let declaration = scan::definition(function, value, work)?;
            return self.materialize(declaration, work);
        };
        work.admit(1, size_of::<ValueId>() + size_of::<usize>())?;
        let mut cursor = first;
        let mut budget = scan::borrow_count(function, work)?;
        loop {
            let Some(operand) = scan::borrow_operand(function, cursor, work)? else {
                break;
            };
            work.admit(1, size_of::<usize>() + size_of::<ValueId>())?;
            if budget == 0 {
                return self.materialize(Some(Definition::Value(Inferred::Ptr)), work);
            }
            budget -= 1;
            cursor = operand;
        }
        // The chain decision is complete before the original root declaration
        // lookup. An absent root is still a typed conservative borrow (Ptr).
        let declaration = scan::definition(function, cursor, work)?;
        self.borrow_type(declaration, work)
    }
    fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<Option<Ty>>())?;
        if self.pending.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn materialize<O: ExecutionObserver>(
        &mut self,
        declaration: Option<Definition<'_>>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        if let Some(declaration) = declaration {
            self.pending = Some(match declaration {
                Definition::Borrow(_) => Inferred::Ptr.make(work)?,
                Definition::Value(inferred) => inferred.make(work)?,
            });
        }
        Ok(())
    }
    fn borrow_type<O: ExecutionObserver>(
        &mut self,
        declaration: Option<Definition<'_>>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        // Only a declared unrefined FatPtr can survive borrow_result_ty.
        // Comparison results, Ptr/Bool, refined fat and absent roots normalize
        // without constructing/discarding an owned temporary declaration.
        let fat = match declaration {
            Some(Definition::Value(Inferred::Borrowed(ty @ Ty::FatPtr(_)))) => Some(ty),
            _ => None,
        };
        self.pending = Some(trust_ir::bridge::borrow_result_ty_observed(
            fat,
            work.session,
            work.site,
        )?);
        Ok(())
    }
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.session.retirement_step(work.site, 1);
        if let Some(ty) = self.pending.take() {
            let _ = ty.retire_observed(work.session, work.site);
        }
        work.session.retirement_poll(work.site);
    }
}
