// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn source_id(&mut self, text: &str) -> R<bool> {
        self.admit(3, 2 * size_of::<usize>())?;
        if text.is_empty() || text.len() > PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES {
            return self.publish_value(false);
        }
        // `trim()==text` is exactly no whitespace at either nonempty endpoint.
        // Both decodes are bounded to one Unicode scalar; interior controls
        // are then classified by the actual same-owner scalar walk below.
        self.admit(8, 2 * size_of::<Option<char>>())?;
        let first = text
            .chars()
            .next()
            .ok_or(ObservedValueError::InvalidRange)?;
        let last = text
            .chars()
            .next_back()
            .ok_or(ObservedValueError::InvalidRange)?;
        self.admit(16 * u32::BITS as usize, 2 * size_of::<bool>())?;
        if first.is_whitespace() || last.is_whitespace() {
            return self.publish_value(false);
        }
        let mut remaining = text;
        loop {
            self.admit(4, size_of::<Option<char>>())?;
            let Some(ch) = remaining.chars().next() else {
                return self.publish_value(true);
            };
            self.admit(8 * u32::BITS as usize, size_of::<bool>())?;
            if ch.is_control() {
                return self.publish_value(false);
            }
            remaining = &remaining[ch.len_utf8()..];
        }
    }
    pub(super) fn public_id(&mut self, text: &str) -> R<bool> {
        self.admit(3, 2 * size_of::<usize>())?;
        if text.is_empty() || text.len() > PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES {
            return self.publish_value(false);
        }
        let mut at = 0usize;
        while let Some(byte) = self.at(text.as_bytes(), at)? {
            self.admit(4, size_of::<bool>())?;
            if !byte.is_ascii_graphic() || matches!(*byte, b'?' | b'#') {
                return self.publish_value(false);
            }
            self.next(&mut at)?;
        }
        self.publish_value(true)
    }
    pub(super) fn first_public(&mut self, module: &Module, end: usize, id: &str) -> R<Option<u32>> {
        let mut at = 0usize;
        while at < end {
            let row = self
                .at(&module.proof_obligations, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            self.admit(1, size_of::<Option<&ProofObligationSourceIdentity>>())?;
            if let Some(source) = &row.source {
                self.admit(
                    1,
                    size_of::<Option<&trust_ir::proof::PublicObligationIdentity>>(),
                )?;
                if let Some(public) = &source.public
                    && self.equal(&public.obligation_id, id)?
                {
                    return self.publish_value(Some(row.id.index()));
                }
            }
            self.next(&mut at)?;
        }
        self.publish_value(None)
    }
}
