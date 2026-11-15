// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn write<O: ExecutionObserver>(
    error: &CompletenessError,
    work: &mut Work<'_, '_, O>,
    output: &mut String,
) -> R {
    work.admit(2, size_of::<&CompletenessError>())?;
    match error {
        CompletenessError::IncompletenessUnclaimed => work.text("the module makes no completeness claim (Module.completeness is None); a consumer that needs a complete module refuses it, never assumes it", output),
        CompletenessError::ModuleIncomplete { rows } => {
            work.text("the module claims to be partial: ", output)?;
            work.number(rows.len(), output)?;
            work.text(" unlowered item(s)", output)?;
            let mut index = 0usize;
            loop {
                work.admit(1, size_of::<Option<&UnloweredRow>>())?;
                let Some(row) = rows.get(index) else { return Ok(()) };
                work.admit(3, size_of::<UnloweredRow>())?;
                let UnloweredRow { symbol, display_path, reason } = row;
                work.text("; ", output)?;
                work.quoted(symbol, output)?;
                work.admit(1, size_of::<Option<&str>>())?;
                match display_path {
                    None => {},
                    Some(path) => {
                        work.text(" (", output)?;
                        work.text(path, output)?;
                        work.text(")", output)?;
                    }
                }
                work.text(": ", output)?;
                work.text(reason, output)?;
                work.next(&mut index)?;
            }
        }
    }
}
