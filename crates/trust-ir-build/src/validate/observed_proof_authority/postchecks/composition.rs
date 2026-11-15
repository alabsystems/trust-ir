// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::proof::ProofEvidence;
impl Post {
    pub(super) fn composition<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        catalog: &ModuleFunctionCatalog<'_>,
        rows: &[TvRechecked],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(entry) = w.at(rows, at)? {
            self.entry(module, catalog, rows, at, entry, w)?;
            w.next(&mut at)?;
        }
        self.cycles(catalog, rows, w)
    }
    fn entry<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        catalog: &ModuleFunctionCatalog<'_>,
        rows: &[TvRechecked],
        position: usize,
        entry: &TvRechecked,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(certificate) = w.at(&module.proof_certificates, at)? {
            w.admit(4, size_of::<bool>())?;
            if certificate.obligation == entry.obligation
                && let ProofEvidence::InheritedFromCallee {
                    callee,
                    obligation,
                    external,
                } = &certificate.evidence
            {
                self.edge(
                    catalog,
                    rows,
                    position,
                    entry,
                    *callee,
                    *obligation,
                    external.is_some(),
                    w,
                )?;
            }
            w.next(&mut at)?;
        }
        let mut at = 0;
        while let Some(callee) = w.at(&entry.callees, at)? {
            if !contains(&self.scratch.named, *callee, w)? {
                self.missing(catalog, entry, *callee, w)?;
            }
            w.next(&mut at)?;
        }
        w.rows(take(&mut self.scratch.named));
        Ok(())
    }
    fn edge<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        rows: &[TvRechecked],
        position: usize,
        entry: &TvRechecked,
        callee: FuncId,
        obligation: ProofId,
        external: bool,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        if external {
            return self.imported(catalog, entry, callee, w);
        }
        if !contains(&entry.callees, callee, w)? {
            return self.uncalled(catalog, entry, callee, w);
        }
        if contains(&self.scratch.named, callee, w)? {
            return self.repeated(catalog, entry, callee, w);
        }
        w.push(&mut self.scratch.named, callee)?;
        let mut target = None;
        let mut ambiguous = false;
        let mut at = 0;
        while let Some(other) = w.at(rows, at)? {
            w.admit(4, size_of::<Option<usize>>() + size_of::<bool>())?;
            if other.obligation == obligation {
                if target.is_some() {
                    ambiguous = true;
                } else {
                    target = Some(at);
                }
            }
            w.next(&mut at)?;
        }
        w.admit(4, size_of::<Option<usize>>())?;
        let grounded = match target {
            Some(target) if !ambiguous => {
                let row = w
                    .at(rows, target)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                if row.function == callee {
                    Some(target)
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(target) = grounded {
            w.push(&mut self.scratch.edges, (position, target))
        } else {
            self.ungrounded(catalog, entry, callee, obligation, w)
        }
    }
}
fn contains<O: ExecutionObserver>(rows: &[FuncId], id: FuncId, w: &mut Work<'_, '_, O>) -> R<bool> {
    let mut at = 0;
    while let Some(other) = w.at(rows, at)? {
        w.admit(1, size_of::<bool>())?;
        if *other == id {
            return Ok(true);
        }
        w.next(&mut at)?;
    }
    Ok(false)
}
