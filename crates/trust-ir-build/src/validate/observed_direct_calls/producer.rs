// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn render<O: ExecutionObserver>(
    source: &Option<Producer>,
    output: &mut Option<String>,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, size_of::<Option<String>>())?;
    if output.is_some() {
        return Err(ObservedValueError::InvalidRange);
    }
    let Some(producer) = source else {
        return Ok(());
    };
    work.admit(6, size_of::<String>())?;
    *output = Some(String::new());
    let text = output.as_mut().ok_or(ObservedValueError::InvalidRange)?;
    match producer {
        Producer::TRust => work.text("trust", text),
        Producer::Clean => work.text("clean", text),
        Producer::TrustIr => work.text("trust-ir", text),
        Producer::TSwift => work.text("tswift", text),
        Producer::TC => work.text("tc", text),
        Producer::Other(raw) => work.quoted(raw, text),
    }
}
