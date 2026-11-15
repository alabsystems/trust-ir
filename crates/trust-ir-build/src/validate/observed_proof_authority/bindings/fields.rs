// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Binding {
    pub(super) fn digest<O: ExecutionObserver>(
        &mut self,
        digest: ProofDigest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(2, size_of::<ProofDigest>())?;
        self.text(
            match digest.algorithm {
                ProofDigestAlgorithm::Sha256 => "sha256:",
                ProofDigestAlgorithm::TrustIrStableV1 => "trust_ir-stable-v1:",
            },
            w,
        )?;
        let mut at = 0;
        while let Some(byte) = w.at(&digest.bytes, at)? {
            w.admit(8, 2)?;
            let hex = b"0123456789abcdef";
            let digits = [hex[(byte >> 4) as usize], hex[(byte & 15) as usize]];
            let text =
                core::str::from_utf8(&digits).map_err(|_| ObservedValueError::InvalidRange)?;
            self.text(text, w)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    pub(super) fn strings<O: ExecutionObserver>(
        &mut self,
        rows: &[String],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.text("[", w)?;
        let mut at = 0;
        while let Some(row) = w.at(rows, at)? {
            if at != 0 {
                self.text(", ", w)?;
            }
            self.quoted(row, w)?;
            w.next(&mut at)?;
        }
        self.text("]", w)
    }
    pub(super) fn callees_equal<O: ExecutionObserver>(
        &self,
        a: &[String],
        b: &[String],
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(2, 2 * size_of::<usize>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        let mut at = 0;
        while let Some(a) = w.at(a, at)? {
            let b = w.at(b, at)?.ok_or(ObservedValueError::InvalidRange)?;
            if !w.text_equal(a, b)? {
                return Ok(false);
            }
            w.next(&mut at)?;
        }
        Ok(true)
    }
}
