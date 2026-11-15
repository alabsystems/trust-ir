// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn failed_rows<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut row = 0;
        while let Some(obligation) = work.at(&module.proof_obligations, row)? {
            work.admit(2, 0)?;
            if obligation.function == Some(function.id) {
                work.admit(4, size_of::<Option<ContractClauseRole>>())?;
                if ContractClauseRole::backed_by_kind(&obligation.kind).is_some() {
                    // This original five-cell classifier has no variable payload.
                    work.admit(6, 0)?;
                    if !obligation.status.is_discharged_tier()
                        && obligation.status == ProofStatus::Failed
                    {
                        self.failed_detail(obligation.id.index(), work)?;
                        self.issue(function, work)?;
                    }
                }
            }
            work.next(&mut row)?;
        }
        Ok(())
    }
    pub(super) fn has_backing<O: ExecutionObserver>(
        module: &Module,
        function: &Function,
        role: ContractClauseRole,
        clause: &ProofFormula,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut row = 0;
        while let Some(obligation) = work.at(&module.proof_obligations, row)? {
            work.admit(2, 0)?;
            if obligation.function == Some(function.id) {
                work.admit(4, size_of::<Option<ContractClauseRole>>())?;
                let row_role = ContractClauseRole::backed_by_kind(&obligation.kind);
                work.admit(6, 0)?;
                if row_role == Some(role) && obligation.status.is_discharged_tier() {
                    work.admit(1, size_of::<Option<&ProofFormula>>())?;
                    if let Some(formula) = &obligation.formula
                        && formula.structurally_eq_observed(clause, work.session, work.site)?
                    {
                        work.admit(1, size_of::<bool>())?;
                        return Ok(true);
                    }
                }
            }
            work.next(&mut row)?;
        }
        work.admit(1, size_of::<bool>())?;
        Ok(false)
    }
}
