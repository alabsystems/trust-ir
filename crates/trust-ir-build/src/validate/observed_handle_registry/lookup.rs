// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl HandleRegistry {
    /// Exact original first (physical pin, physical entry) symbol match. Walk
    /// actual supplied rows and compare complete bounded byte chunks; do not
    /// construct a registry, read entry contracts or grant runtime authority.
    /// A stop returns no absence/match fallback. No owner/grant/deadline/TLS/
    /// fuel reset; only borrowed fixed descriptors are retained and retired.
    pub(crate) fn entry_for_symbol_observed<O: ExecutionObserver>(
        &self,
        symbol: &str,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<(&HandleRuntimePin, &HandleEntryPoint)>> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Work<'_, '_, O>>() + 2 * size_of::<usize>())?;
        let result = lookup(self, symbol, &mut work);
        work.step(size_of::<Work<'_, '_, O>>() + 2 * size_of::<usize>());
        work.poll();
        result
            .and_then(|value| {
                work.publication(size_of::<Option<(&HandleRuntimePin, &HandleEntryPoint)>>())?;
                Ok(value)
            })
            .map_err(|e| work.terminal(e))
    }
}
fn lookup<'a, O: ExecutionObserver>(
    registry: &'a HandleRegistry,
    symbol: &str,
    work: &mut Work<'_, '_, O>,
) -> R<Option<(&'a HandleRuntimePin, &'a HandleEntryPoint)>> {
    let mut pin_at = 0usize;
    while let Some(pin) = work.at(&registry.pins, pin_at)? {
        work.admit(1, size_of::<&[HandleEntryPoint]>() + size_of::<usize>())?;
        let mut entry_at = 0usize;
        while let Some(entry) = work.at(pin.entry_points, entry_at)? {
            work.admit(1, size_of::<&str>())?;
            if work.equal(entry.symbol, symbol)? {
                work.admit(
                    1,
                    size_of::<Option<(&HandleRuntimePin, &HandleEntryPoint)>>(),
                )?;
                return Ok(Some((pin, entry)));
            }
            work.next(&mut entry_at)?;
        }
        work.next(&mut pin_at)?;
    }
    work.admit(
        1,
        size_of::<Option<(&HandleRuntimePin, &HandleEntryPoint)>>(),
    )?;
    Ok(None)
}
