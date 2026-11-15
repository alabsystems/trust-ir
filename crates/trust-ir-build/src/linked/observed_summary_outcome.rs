// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Borrow the already-recorded outcome; this code can mint no authentication.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::size_of;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
#[cfg(test)]
mod handle_tests;
#[cfg(test)]
mod tests;
impl AuthenticatedImports {
    pub(crate) fn backed_by_outcome_observed<O: ExecutionObserver>(
        &self,
        function: FuncId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Option<&SiteOutcome>, ObservedValueError> {
        recorded_outcome_observed(&self.backed_by, function, session, site)
    }

    /// Borrow only the exact linked walk's retained handle declaration outcome.
    /// No import authentication, new owner or default outcome is manufactured.
    pub(crate) fn handle_declaration_outcome_observed<O: ExecutionObserver>(
        &self,
        function: FuncId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Option<&SiteOutcome>, ObservedValueError> {
        recorded_outcome_observed(&self.handle_declarations, function, session, site)
    }
}

fn recorded_outcome_observed<'a, O: ExecutionObserver>(
    map: &'a BTreeMap<u32, SiteOutcome>,
    function: FuncId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<Option<&'a SiteOutcome>, ObservedValueError> {
    // Fixed-key B-tree cursor work is conservatively population-priced.
    // Its installed std implementation is an explicit scalar boundary;
    // the actual map scan has a callback at every cursor advance.
    let population = map
        .len()
        .checked_add(1)
        .ok_or(ObservedValueError::CapacityOverflow)?;
    step(
        session,
        site,
        population,
        size_of::<std::collections::btree_map::Iter<'_, u32, SiteOutcome>>(),
    )?;
    let mut rows = map.iter();
    let answer = loop {
        step(
            session,
            site,
            population,
            size_of::<Option<(&u32, &SiteOutcome)>>(),
        )?;
        let Some((key, outcome)) = rows.next() else {
            break None;
        };
        step(session, site, 1, 2 * size_of::<u32>())?;
        if *key == function.index() {
            break Some(outcome);
        }
        if *key > function.index() {
            break None;
        }
    };
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Publication,
        site,
        work: 1,
        copy_bytes: size_of::<Option<&SiteOutcome>>(),
    })?;
    Ok(answer)
}
fn step<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    copy_bytes: usize,
) -> Result<(), ObservedValueError> {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work,
            copy_bytes,
        })
        .map_err(Into::into)
}
