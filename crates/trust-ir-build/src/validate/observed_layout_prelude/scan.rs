// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
enum Table {
    Tuple,
    Closure,
}
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.table.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.table = Some(LayoutTable::new_observed(module, work.session, work.site)?);
        self.check(Table::Tuple, work)?;
        self.check(Table::Closure, work)
    }
    fn check<O: ExecutionObserver>(&mut self, kind: Table, work: &mut Work<'_, '_, O>) -> R {
        work.admit(3, 0)?;
        if self.pending.is_some() || self.spelled.capacity() != 0 || self.reason.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let table = self
            .table
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let outcome = match kind {
            Table::Tuple => table.validate_tuple_layouts_observed(work.session, work.site)?,
            Table::Closure => table.validate_closure_layouts_observed(work.session, work.site)?,
        };
        if let Err(error) = outcome {
            // Retain the actual owned semantic error before any further poll,
            // formatting, allocation or output construction can refuse.
            self.pending = Some(error);
            self.spelled = self
                .pending
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .display_observed(work.session, work.site)?;
            if matches!(kind, Table::Closure) {
                work.text(CLOSURE_LAYOUT_TABLE_REASON_PREFIX, &mut self.reason)?;
            }
            work.text(&self.spelled, &mut self.reason)?;
            work.retire_text(&mut self.spelled);
            work.admit(1, 0)?;
            self.retire_error(work);
            work.admit(1, 0)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::TupleLayoutInconsistent {
                reason: take(&mut self.reason),
            });
        }
        Ok(())
    }
}
