// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn path<O: ExecutionObserver>(value: Option<String>, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<Option<String>>().saturating_add(1));
    match value {
        None => work.fixed(()),
        Some(text) => work.retire_text(text),
    }
}
pub(super) fn row<O: ExecutionObserver>(value: UnloweredRow, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<UnloweredRow>().saturating_add(1));
    let UnloweredRow {
        symbol,
        display_path,
        reason,
    } = value;
    work.retire_text(symbol);
    path(display_path, work);
    work.retire_text(reason);
    work.poll();
}
pub(super) fn rows<O: ExecutionObserver>(
    mut values: Vec<UnloweredRow>,
    work: &mut Work<'_, '_, O>,
) {
    loop {
        work.step(size_of::<Option<UnloweredRow>>().saturating_add(1));
        let Some(value) = values.pop() else { break };
        row(value, work);
    }
    work.step(size_of::<Vec<UnloweredRow>>().saturating_add(1));
    drop(values);
    work.poll();
}
pub(super) fn error<O: ExecutionObserver>(value: CompletenessError, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<CompletenessError>().saturating_add(1));
    match value {
        CompletenessError::IncompletenessUnclaimed => work.fixed(()),
        CompletenessError::ModuleIncomplete { rows: values } => rows(values, work),
    }
    work.poll();
}
pub(super) fn outcome<O: ExecutionObserver>(
    value: Result<(), CompletenessError>,
    work: &mut Work<'_, '_, O>,
) {
    work.step(size_of::<Result<(), CompletenessError>>().saturating_add(1));
    match value {
        Ok(unit) => work.fixed(unit),
        Err(value) => error(value, work),
    }
}
