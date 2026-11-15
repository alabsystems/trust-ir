// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn exists(&mut self, module: &Module, id: ProofId) -> R<bool> {
        let mut at = 0usize;
        while let Some(row) = self.at(&module.proof_obligations, at)? {
            self.admit(1, 2 * size_of::<ProofId>())?;
            if row.id == id {
                return self.value(true);
            }
            self.next(&mut at)?;
        }
        self.value(false)
    }
    pub(super) fn unique<'m>(
        &mut self,
        module: &'m Module,
        id: ProofId,
    ) -> R<Option<&'m ProofObligation>> {
        self.admit(1, size_of::<Option<&ProofObligation>>())?;
        let mut found = None;
        let mut at = 0usize;
        while let Some(row) = self.at(&module.proof_obligations, at)? {
            self.admit(
                2,
                2 * size_of::<ProofId>() + size_of::<Option<&ProofObligation>>(),
            )?;
            if row.id == id {
                if found.is_some() {
                    return self.value(None);
                }
                found = Some(row);
            }
            self.next(&mut at)?;
        }
        self.value(found)
    }
    pub(super) fn justified(&mut self, module: &Module, id: ProofId) -> R<bool> {
        let mut at = 0usize;
        while let Some(cert) = self.at(&module.proof_certificates, at)? {
            self.admit(1, 2 * size_of::<ProofId>())?;
            if cert.obligation == id {
                self.admit(8, size_of::<Option<&str>>())?;
                if let ProofEvidence::Trusted(text) = &cert.evidence
                    && self.nonblank(text)?
                {
                    return self.value(true);
                }
            }
            self.next(&mut at)?;
        }
        self.value(false)
    }
    fn nonblank(&mut self, mut text: &str) -> R<bool> {
        loop {
            self.admit(4, size_of::<Option<char>>() + size_of::<&str>())?;
            let Some(ch) = text.chars().next() else {
                return self.value(false);
            };
            self.admit(8 * u32::BITS as usize, size_of::<bool>())?;
            if !ch.is_whitespace() {
                return self.value(true);
            }
            self.admit(2, size_of::<&str>() + size_of::<usize>())?;
            text = &text[ch.len_utf8()..];
        }
    }
}
