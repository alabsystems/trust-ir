// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn binding<O: ExecutionObserver>(
        &mut self,
        obligation: &ProofObligation,
        name: &str,
        binding: &ClauseBinding,
        index: u32,
        primed: bool,
        resolved: Resolved<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some((machine, property)) = resolved else {
            self.prefix(name, index, primed, work)?;
            work.text(
                ", a spec-machine state variable; that index space belongs to a SpecModule's `vars`, which a module obligation has only through a RESOLVING `spec` backref to one of that machine's temporal properties, and this obligation has none",
                &mut self.detail)?;
            return self.emit(obligation, work);
        };
        work.admit(1, size_of::<usize>())?;
        let at = usize::try_from(index).map_err(|_| ObservedValueError::CapacityOverflow)?;
        let Some(variable) = work.at(&machine.vars, at)? else {
            self.prefix(name, index, primed, work)?;
            work.text(", but machine ", &mut self.detail)?;
            work.quoted(&machine.name, &mut self.detail)?;
            work.text(" declares ", &mut self.detail)?;
            work.number(machine.vars.len() as u128, &mut self.detail)?;
            work.text(" state variable(s)", &mut self.detail)?;
            return self.emit(obligation, work);
        };
        // Header admission precedes the real child. Store its complete owned
        // result before any further fallible formatting/allocation/publication.
        work.admit(1, size_of::<Option<String>>())?;
        if self.sort.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.sort =
            variable.effective_sort_mismatch_observed(&binding.sort, work.session, work.site)?;
        work.admit(1, size_of::<bool>())?;
        if self.sort.is_some() {
            self.prefix(name, index, primed, work)?;
            work.text(" (", &mut self.detail)?;
            work.quoted(&variable.name, &mut self.detail)?;
            work.text(") at sort ", &mut self.detail)?;
            work.admit(1, size_of::<String>())?;
            if self.debug.capacity() != 0 {
                return Err(ObservedValueError::InvalidRange);
            }
            self.debug = binding.sort.debug_observed(work.session, work.site)?;
            work.text(&self.debug, &mut self.detail)?;
            work.flat(take(&mut self.debug));
            work.admit(1, 0)?;
            work.text(", but the variable declares sort ", &mut self.detail)?;
            work.text(
                self.sort
                    .as_deref()
                    .ok_or(ObservedValueError::InvalidRange)?,
                &mut self.detail,
            )?;
            self.emit(obligation, work)?;
        }
        self.clear_sort(work)?;
        let mut spelled = 0usize;
        while let Some(other) = work.at(&machine.vars, spelled)? {
            if work.equal(&other.name, name)? {
                work.admit(1, 2 * size_of::<usize>())?;
                if spelled != at {
                    self.prefix(name, index, primed, work)?;
                    work.text(", but ", &mut self.detail)?;
                    work.quoted(name, &mut self.detail)?;
                    work.text(" is the name of state variable ", &mut self.detail)?;
                    work.number(spelled as u128, &mut self.detail)?;
                    work.text(" (", &mut self.detail)?;
                    work.quoted(&other.name, &mut self.detail)?;
                    work.text(") of machine ", &mut self.detail)?;
                    work.quoted(&machine.name, &mut self.detail)?;
                    work.text(
                        "; one name cannot denote two of that machine's variables",
                        &mut self.detail,
                    )?;
                    self.emit(obligation, work)?;
                }
                break;
            }
            work.next(&mut spelled)?;
        }
        work.admit(6, size_of::<bool>() + size_of::<&str>())?;
        if primed
            && !matches!(
                property.form,
                TemporalForm::WeakFair { .. } | TemporalForm::StrongFair { .. }
            )
        {
            self.prefix(name, index, primed, work)?;
            work.text(
                ", the SUCCESSOR state, but the temporal property ",
                &mut self.detail,
            )?;
            work.quoted(&property.name, &mut self.detail)?;
            work.text(" it discharges is a ", &mut self.detail)?;
            // Fixed five-variant discriminant table only; no carried formulas.
            work.text(property.form.tag(), &mut self.detail)?;
            work.text(" state predicate, not an action relation", &mut self.detail)?;
            self.emit(obligation, work)?;
        }
        Ok(())
    }
}
