// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn rows() -> Vec<UnloweredRow> {
    vec![
        row("first'\"\nλ", None, "raw reason\nλ"),
        row("second", Some(""), ""),
        row(
            "first'\"\nλ",
            Some("crate::中\t()"),
            "later duplicate reason",
        ),
    ]
}
pub(super) fn module() -> Module {
    partial(rows())
}
pub(super) fn errors() -> [CompletenessError; 3] {
    [
        CompletenessError::IncompletenessUnclaimed,
        CompletenessError::ModuleIncomplete { rows: vec![] },
        CompletenessError::ModuleIncomplete {
            rows: vec![row("a'\"", None, "why"), row("b", Some("path"), "reason")],
        },
    ]
}
