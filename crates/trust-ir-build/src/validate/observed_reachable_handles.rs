// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual diagnostic handle closure, ordered uniqueness and complete text.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::{
    cmp::Ordering,
    mem::{size_of, take},
};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod follow;
mod inline;
mod ordered;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy, PartialEq, Eq)]
enum Key {
    Ty(usize),
    Func(usize),
    Struct(u32),
    Enum(u32),
    Record(u32),
    Closure(usize),
}
#[derive(Clone, Copy)]
enum Frame<'a> {
    Visit(&'a Ty),
    Children(&'a [Ty], usize),
}
#[derive(Default)]
struct State<'a> {
    stack: Vec<&'a Ty>,
    frames: Vec<Frame<'a>>,
    seen: Vec<Key>,
    handles: Vec<&'a Ty>,
    pending: String,
    output: String,
}
/// Exact `reachable_handles(module, params.chain(returns))`, followed by the
/// original Handle type display and `", "` join, under the original owner.
/// Actual table/inline traversal, cycle breaking, complete identity comparison,
/// ordered insertion, child display and output copying are interior-observed.
/// Duplicate named definitions all contribute; unknown references add nothing.
///
/// This names diagnostic identities only, never admits a handle/type/runtime/
/// import/module/source/proof. Borrowed temporary nodes stay original-custodied;
/// every full returned display String is immediately held before another fee.
/// Failure consumes all scratch/partial output under sticky retirement and
/// returns no shorter text. Physical allocator/deallocator/OOM/panic/unwind/
/// hard-time bounds and successful original input/result disposal remain OPEN.
pub(super) fn reachable_handles_text_observed<O: ExecutionObserver>(
    module: &Module,
    params: &[Ty],
    returns: &[Ty],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<String> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, params, returns, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.output)),
        Err(error) => {
            work.flat(take(&mut state.output));
            Err(work.terminal(error))
        }
    }
}
impl<'a> State<'a> {
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        params: &'a [Ty],
        returns: &'a [Ty],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.types(params, work)?;
        self.types(returns, work)?;
        while let Some(ty) = work.pop(&mut self.stack)? {
            self.inline(module, ty, work)?;
        }
        let mut at = 0usize;
        while let Some(ty) = work.at(&self.handles, at)? {
            work.admit(1, size_of::<&Ty>())?;
            let ty = *ty;
            self.pending = ty.display_observed(work.session, work.site)?;
            if at != 0 {
                work.text(", ", &mut self.output)?;
            }
            work.text(&self.pending, &mut self.output)?;
            work.flat(take(&mut self.pending));
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_copy(&mut self.stack);
        work.retire_copy(&mut self.frames);
        work.retire_copy(&mut self.seen);
        work.retire_copy(&mut self.handles);
        work.flat(take(&mut self.pending));
    }
    fn types<O: ExecutionObserver>(&mut self, types: &'a [Ty], work: &mut Work<'_, '_, O>) -> R {
        let mut at = 0usize;
        while let Some(ty) = work.at(types, at)? {
            work.push(&mut self.stack, ty)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn fields<O: ExecutionObserver>(
        &mut self,
        fields: &'a [trust_ir::FieldDef],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0usize;
        while let Some(field) = work.at(fields, at)? {
            work.admit(1, size_of::<&Ty>())?;
            work.push(&mut self.stack, &field.ty)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
}
