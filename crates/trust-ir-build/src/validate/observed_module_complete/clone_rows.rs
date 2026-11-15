// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(3, size_of::<Option<&ModuleCompleteness>>())?;
        match &module.completeness {
            None => {
                work.admit(1, size_of::<Result<(), CompletenessError>>())?;
                self.outcome = Err(CompletenessError::IncompletenessUnclaimed);
            }
            Some(ModuleCompleteness::Complete) => {
                work.admit(1, size_of::<Result<(), CompletenessError>>())?;
                self.outcome = Ok(());
            }
            Some(ModuleCompleteness::Partial(rows)) => {
                self.copy_rows(rows, work)?;
                work.admit(1, size_of::<Result<(), CompletenessError>>())?;
                self.outcome = Err(CompletenessError::ModuleIncomplete {
                    rows: take(&mut self.rows),
                });
            }
        }
        Ok(())
    }
    pub(super) fn copy_rows<O: ExecutionObserver>(
        &mut self,
        rows: &[UnloweredRow],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<Option<&UnloweredRow>>())?;
            let Some(row) = rows.get(index) else {
                return Ok(());
            };
            self.copy_row(row, work)?;
            work.next(&mut index)?;
        }
    }
    fn copy_row<O: ExecutionObserver>(
        &mut self,
        row: &UnloweredRow,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(4, size_of::<UnloweredRow>())?;
        // No rest: every future field must acquire real copy/cleanup handling.
        let UnloweredRow {
            symbol,
            display_path,
            reason,
        } = row;
        if self.symbol.capacity() != 0 || self.path.is_some() || self.reason.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text(symbol, &mut self.symbol)?;
        work.admit(1, size_of::<Option<String>>())?;
        match display_path {
            None => {}
            Some(path) => {
                // Own the empty header before the first fallible text copy.
                self.path = Some(String::new());
                match self.path.as_mut() {
                    Some(output) => work.text(path, output)?,
                    None => return Err(ObservedValueError::InvalidRange),
                }
            }
        }
        work.text(reason, &mut self.reason)?;
        work.reserve(&mut self.rows)?;
        work.admit(1, size_of::<UnloweredRow>())?;
        self.rows.push(UnloweredRow {
            symbol: take(&mut self.symbol),
            display_path: self.path.take(),
            reason: take(&mut self.reason),
        });
        Ok(())
    }
}
