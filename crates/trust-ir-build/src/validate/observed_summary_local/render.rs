// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    fn role_text<O: ExecutionObserver>(
        &mut self,
        role: ContractClauseRole,
        kind: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Fixed three-way static spellings; no dynamic formatter.
        work.admit(3, size_of::<&str>())?;
        work.text(
            if kind {
                role.backing_kind_name()
            } else {
                role.name()
            },
            &mut self.detail,
        )
    }
    pub(super) fn duplicate_detail<O: ExecutionObserver>(
        &mut self,
        role: ContractClauseRole,
        index: usize,
        first: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.role_text(role, false, work)?;
        work.text(" clause ", &mut self.detail)?;
        work.number(index as u128, &mut self.detail)?;
        work.text(" duplicates clause ", &mut self.detail)?;
        work.number(first as u128, &mut self.detail)
    }
    pub(super) fn failed_detail<O: ExecutionObserver>(
        &mut self,
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(
            "summary claims `proved` while contract obligation #",
            &mut self.detail,
        )?;
        work.number(id as u128, &mut self.detail)?;
        work.text(", scoped to this function, is Failed", &mut self.detail)
    }
    pub(super) fn declaration_detail<O: ExecutionObserver>(
        &mut self,
        role: ContractClauseRole,
        count: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("summary claims `proved` with ", &mut self.detail)?;
        work.number(count as u128, &mut self.detail)?;
        work.text(" ", &mut self.detail)?;
        self.role_text(role, false, work)?;
        work.text(" clause(s) but no local ", &mut self.detail)?;
        self.role_text(role, true, work)?;
        work.text(" obligation can back a clause here: a body-less declaration has no body a local obligation could be about, so its contract is proved only where it is defined and must cite that module with `backed_by`; `backed_by: None` is NOT RECORDED", &mut self.detail)
    }
    pub(super) fn missing_detail<O: ExecutionObserver>(
        &mut self,
        role: ContractClauseRole,
        index: usize,
        clause: &ProofFormula,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.role_text(role, false, work)?;
        work.text(" clause ", &mut self.detail)?;
        work.number(index as u128, &mut self.detail)?;
        work.text(" `", &mut self.detail)?;
        // The exact original clause_text rule, including Some(""). No owned
        // intermediate string can escape custody between render and outer text.
        work.admit(1, size_of::<Option<&str>>())?;
        match &clause.smtlib {
            Some(text) => work.text(text, &mut self.detail)?,
            None => {
                work.text("[", &mut self.detail)?;
                work.text(&clause.schema, &mut self.detail)?;
                work.text("] ", &mut self.detail)?;
                work.text(&clause.payload, &mut self.detail)?;
            }
        }
        work.text("` has no Discharged/Certified ", &mut self.detail)?;
        self.role_text(role, true, work)?;
        work.text(" row scoped to this function stating exactly this clause (rows stating other clauses do not count)", &mut self.detail)
    }
}
