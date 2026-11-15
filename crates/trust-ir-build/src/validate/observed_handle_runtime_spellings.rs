// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original handle/structural-runtime namespace rule under original ownership.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    def: String,
    runtime: String,
    errors: Vec<ValidationError>,
}
/// Exact original structural-definition spelling diagnostic. The full module
/// census still decides whether this handle-bearing-only rule is invoked.
/// Actual struct/enum/record order, every registry row and full raw runtime
/// comparison are observed; unrelated definition/entry-point payloads unread.
/// No lexical/pinned-runtime/type/module/source/proof authority is created.
///
/// Both complete/partial output fields and prior errors remain original-owned
/// through every fee and retire exhaustively on refusal. No owner, deadline,
/// grant, TLS or fuel reset; physical hard bounds and successful original
/// input/result disposal remain OPEN.
pub(super) fn validate_handle_runtime_spellings_observed<O: ExecutionObserver>(
    module: &Module,
    registry: &HandleRegistry,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, registry, &mut work);
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
        registry: &HandleRegistry,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0usize;
        while let Some(row) = work.at(&module.structs, at)? {
            work.admit(1, size_of::<u32>() + size_of::<&str>())?;
            self.definition("struct", row.id.index(), &row.name, registry, work)?;
            work.next(&mut at)?;
        }
        at = 0;
        while let Some(row) = work.at(&module.enums, at)? {
            work.admit(1, size_of::<u32>() + size_of::<&str>())?;
            self.definition("enum", row.id.index(), &row.name, registry, work)?;
            work.next(&mut at)?;
        }
        at = 0;
        while let Some(row) = work.at(&module.records, at)? {
            work.admit(1, size_of::<u32>() + size_of::<&str>())?;
            self.definition("record", row.id.index(), &row.name, registry, work)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn definition<O: ExecutionObserver>(
        &mut self,
        kind: &'static str,
        id: u32,
        name: &str,
        registry: &HandleRegistry,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<&[HandleRuntimePin]>())?;
        let pins = registry.pins();
        let mut at = 0usize;
        while let Some(pin) = work.at(pins, at)? {
            work.admit(1, size_of::<&str>())?;
            if work.equal(pin.runtime, name)? {
                work.text(kind, &mut self.def)?;
                work.text(" #", &mut self.def)?;
                work.number(id, &mut self.def)?;
                work.text(pin.runtime, &mut self.runtime)?;
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
                self.errors
                    .push(ValidationError::HandleRuntimeSpelledStructurally {
                        def: take(&mut self.def),
                        runtime: take(&mut self.runtime),
                    });
                // The original find chooses only the first matching pin.
                return Ok(());
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.def));
        work.flat(take(&mut self.runtime));
    }
}
