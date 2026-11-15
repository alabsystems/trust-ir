// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original module enum-tag switch coverage, not the shape-only rule.
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
use trust_ir::ty::EnumDef;
use trust_ir::value::EnumId;
mod cases;
mod definitions;
mod scan;
mod selector;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Widen {
    Zero { to: u32 },
    Sign { from: u32, to: u32 },
}
#[derive(Clone, Copy)]
struct Selection<'m> {
    definition: &'m EnumDef,
    width: u32,
}
#[derive(Default)]
struct State<'f, 'm> {
    definitions: Vec<(u32, usize, &'f Inst)>,
    widen: Vec<Widen>,
    selection: Option<Selection<'m>>,
    discriminants: Vec<i128>,
    disc_bits: Vec<u128>,
    covered: Vec<u128>,
    enum_ty: String,
    literal: String,
    reason: String,
    here: String,
    errors: Vec<ValidationError>,
}
/// Complete original Rule2 only: the flagged actual last terminator's enum tag,
/// unique definitions, Copy/value-preserving widening provenance, transformed
/// discriminants and omitted inhabited variants. This is not Rule1/default/SSA/
/// type/canonical/source/module/proof authority. Source map/function and their
/// disposal remain mandatory original caller identities, not candidate data.
/// All actual work/children/errors stay same-session/site/fuel, held across each
/// fallible fee and full cleanup. No owner/grant/deadline/TLS/flag/fallback.
pub(super) fn validate_exhaustive_switch_cases_observed<O: ExecutionObserver>(
    layouts: &trust_ir::LayoutTable<'_>,
    function: &Function,
    values: &ObservedValueTypes,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_, '_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(layouts, function, values, &mut work);
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
impl State<'_, '_> {
    fn retire_selection<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.fixed(self.selection.take());
        w.rows(take(&mut self.widen));
        w.rows(take(&mut self.discriminants));
        w.rows(take(&mut self.disc_bits));
        w.rows(take(&mut self.covered));
        w.flat(take(&mut self.enum_ty));
        w.flat(take(&mut self.literal));
        w.flat(take(&mut self.reason));
        w.flat(take(&mut self.here));
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        self.retire_selection(w);
        w.rows(take(&mut self.definitions));
    }
}
