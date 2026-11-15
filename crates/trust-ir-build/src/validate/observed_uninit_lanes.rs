// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original placement rule for every Constant::Uninit carrier.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::Block;
use trust_ir::constant::ConstantChildren;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
const EXPECTED: &str = "`uninit` only as a direct lane of an Inst::Const struct/tuple aggregate";
#[derive(Default)]
struct State<'a> {
    frames: Vec<ConstantChildren<'a>>,
    pending: Option<ConstantChildren<'a>>,
    location: String,
    expected: String,
    actual: String,
    render: Option<String>,
    errors: Vec<ValidationError>,
}
/// Execute the entire ordinary Uninit placement constituent with exact ordered
/// diagnostics. A direct Struct/Tuple aggregate lane alone may be Uninit;
/// nested constants, all other Const types, globals and switch cases preserve
/// the original first-hit rules. Child traversal is actual borrowed stored
/// preorder, not a prewalk followed by an opaque recursive formatter.
///
/// All reads, scratch growth, type/constant formatting, child-result custody,
/// diagnostic transport, retirement and publication reuse this original owner
/// and site. No partial vector or accepting substitute escapes a refusal.
/// This is diagnostic data, not whole-module/source/proof authority.
pub(crate) fn validate_module_uninit_lanes_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.walk(module, &mut work);
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
impl State<'_> {
    fn emit<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.text(EXPECTED, &mut self.expected)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
        self.errors.push(ValidationError::ConstTypeMismatch {
            location: take(&mut self.location),
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
        });
        Ok(())
    }
    fn function_location<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: &Block,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("function '", &mut self.location)?;
        work.text(&function.name, &mut self.location)?;
        work.text("' bb", &mut self.location)?;
        work.number(u128::from(block.id.index()), &mut self.location)
    }
    fn copy_render<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<Option<&str>>())?;
        work.text(
            self.render
                .as_deref()
                .ok_or(ObservedValueError::InvalidRange)?,
            &mut self.actual,
        )?;
        work.step(size_of::<Option<String>>().saturating_add(1));
        if let Some(text) = self.render.take() {
            work.flat(text);
        }
        work.admit(1, 0)
    }
    fn constant_detail<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        value: &Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<String>>())?;
        if self.render.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.render = Some(ty.display_observed(work.session, work.site)?);
        self.copy_render(work)?;
        work.text(" constant ", &mut self.actual)?;
        work.admit(1, size_of::<Option<String>>())?;
        self.render = Some(value.display_observed(work.session, work.site)?);
        self.copy_render(work)?;
        work.text(" carries uninit outside a direct lane", &mut self.actual)
    }
    fn retire_frames<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ConstantChildren<'_>>>().saturating_add(1));
        self.pending.take();
        loop {
            work.step(size_of::<Option<ConstantChildren<'_>>>().saturating_add(1));
            if self.frames.pop().is_none() {
                break;
            }
        }
        work.step(size_of::<Vec<ConstantChildren<'_>>>().saturating_add(1));
        drop(take(&mut self.frames));
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_frames(work);
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.step(size_of::<Option<String>>().saturating_add(1));
        if let Some(text) = self.render.take() {
            work.flat(text);
        }
        work.poll();
    }
}
// Successful caller result/input disposal and physical std/allocator/deallocator/
// OOM/panic/unwind/RSS/machine-work/hardtime remain OPEN. No new owner or fuel.
