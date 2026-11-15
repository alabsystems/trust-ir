// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

// Repeating this actual scan avoids an owned duplicate set. The first earlier
// equal formula is still the ordinary error's exact index, and later duplicate
// clauses are still omitted from the final missing-row pass.
fn first_duplicate<O: ExecutionObserver>(
    clauses: &[ProofFormula],
    index: usize,
    clause: &ProofFormula,
    work: &mut Work<'_, '_, O>,
) -> R<Option<usize>> {
    let mut earlier = 0;
    loop {
        work.admit(1, 0)?;
        if earlier >= index {
            return Ok(None);
        }
        let previous = work
            .at(clauses, earlier)?
            .ok_or(ObservedValueError::InvalidRange)?;
        if previous.structurally_eq_observed(clause, work.session, work.site)? {
            work.admit(1, size_of::<Option<usize>>())?;
            return Ok(Some(earlier));
        }
        work.next(&mut earlier)?;
    }
}
impl State {
    pub(super) fn duplicates<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        summary: &FunctionSummary,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut slot = 0;
        while let Some(role) = work.role(slot)? {
            let list = work.clauses(role, summary)?;
            let mut index = 0;
            while let Some(clause) = work.at(list, index)? {
                if let Some(first) = first_duplicate(list, index, clause, work)? {
                    self.duplicate_detail(role, index, first, work)?;
                    self.issue(function, work)?;
                }
                work.next(&mut index)?;
            }
            work.next(&mut slot)?;
        }
        Ok(())
    }
    pub(super) fn missing_rows<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        summary: &FunctionSummary,
        counts_locally: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut slot = 0;
        while let Some(role) = work.role(slot)? {
            let list = work.clauses(role, summary)?;
            work.admit(2, 0)?;
            if !counts_locally {
                if !list.is_empty() {
                    self.declaration_detail(role, list.len(), work)?;
                    self.issue(function, work)?;
                }
            } else {
                let mut index = 0;
                while let Some(clause) = work.at(list, index)? {
                    if first_duplicate(list, index, clause, work)?.is_none()
                        && !Self::has_backing(module, function, role, clause, work)?
                    {
                        self.missing_detail(role, index, clause, work)?;
                        self.issue(function, work)?;
                    }
                    work.next(&mut index)?;
                }
            }
            work.next(&mut slot)?;
        }
        Ok(())
    }
}
