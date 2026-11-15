// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete ordinary per-node builtins then optional frozen schema diagnostics.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::dialect::schema::DialectSchemaRegistry;
use trust_ir::dialect::{AttrValue, DialectInst};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod builtins;
mod schema_errors;
mod schemas;
mod storage;
#[cfg(test)]
mod tests;
mod vector;
mod vector_payload;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'a> {
    qualified: String,
    reason: String,
    temporary: String,
    operand_tys: Vec<&'a Ty>,
    seen: Vec<bool>,
    errors: Vec<ValidationError>,
}
/// Actual builtin decode followed by the optional frozen data-only schema.
/// Supplied SSA rows must be the original containing function's actual observed
/// map; all namespace/signature source is borrowed from this module/registry.
/// Every prior/partial error and complete child String remains owned through
/// original-session refusal and cleanup. No new owner/grant/fuel/callback is
/// created. This is diagnostics only, not module/source/proof authority.
/// Successful output and all borrowed inputs remain the original caller's duty;
/// physical std/allocator/OOM/unwind/stack/time and full module closure are OPEN.
pub(super) fn validate_dialect_node_observed<'a, O: ExecutionObserver>(
    module: &Module,
    node: &'a trust_ir::InstrNode,
    values: &'a ObservedValueTypes,
    schemas: Option<&DialectSchemaRegistry>,
    block: BlockId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, node, values, schemas, block, &mut work);
    state.retire(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(e) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(e))
        }
    }
}
impl<'a> State<'a> {
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        node: &'a trust_ir::InstrNode,
        values: &'a ObservedValueTypes,
        schemas: Option<&DialectSchemaRegistry>,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<&DialectInst>>())?;
        let Inst::DialectOp(op) = &node.inst else {
            return Ok(());
        };
        if !self.builtin(op, values, work)? {
            self.commit(op, block, false, work)?;
        }
        if let Some(registry) = schemas
            && !self.schema(module, op, node.results.len(), values, registry, work)?
        {
            self.commit(op, block, true, work)?;
        }
        Ok(())
    }
    fn commit<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        block: BlockId,
        schema: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(&op.dialect, &mut self.qualified)?;
        work.text(".", &mut self.qualified)?;
        work.text(&op.op, &mut self.qualified)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        let name = take(&mut self.qualified);
        let reason = take(&mut self.reason);
        self.errors.push(if schema {
            ValidationError::InvalidDialectSchema {
                block: block.index(),
                op: name,
                reason,
            }
        } else {
            ValidationError::InvalidVectorDialectOp {
                block: block.index(),
                op: name,
                reason,
            }
        });
        Ok(())
    }
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.qualified));
        work.flat(take(&mut self.reason));
        work.flat(take(&mut self.temporary));
        work.rows(take(&mut self.operand_tys));
        work.rows(take(&mut self.seen));
    }
    fn q<O: ExecutionObserver>(&mut self, op: &DialectInst, work: &mut Work<'_, '_, O>) -> R {
        work.text(&op.dialect, &mut self.reason)?;
        work.text(".", &mut self.reason)?;
        work.text(&op.op, &mut self.reason)
    }
    fn raw_ty<O: ExecutionObserver>(&mut self, ty: &Ty, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<String>())?;
        if self.temporary.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.temporary = ty.debug_observed(work.session, work.site)?;
        work.text(&self.temporary, &mut self.reason)?;
        work.flat(take(&mut self.temporary));
        work.admit(1, 0)
    }
    fn display_ty<O: ExecutionObserver>(&mut self, ty: &Ty, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<String>())?;
        if self.temporary.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.temporary = ty.display_observed(work.session, work.site)?;
        work.text(&self.temporary, &mut self.reason)?;
        work.flat(take(&mut self.temporary));
        work.admit(1, 0)
    }
    fn raw_func<O: ExecutionObserver>(&mut self, ty: &FuncTy, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<String>())?;
        if self.temporary.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.temporary = ty.debug_observed(work.session, work.site)?;
        work.text(&self.temporary, &mut self.reason)?;
        work.flat(take(&mut self.temporary));
        work.admit(1, 0)
    }
}
