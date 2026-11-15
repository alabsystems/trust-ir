// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn import_equal(&mut self, left: &ModuleImport, right: &ModuleImport) -> R<bool> {
        self.admit(4, usize::BITS as usize)?;
        // Intentionally NO rest pattern. The ordinary key is the whole derived
        // ModuleImport Eq, and a new field must fail this source at compile time.
        let ModuleImport {
            name: a,
            digest: ad,
            producer: ap,
            scheme: ascheme,
        } = left;
        let ModuleImport {
            name: b,
            digest: bd,
            producer: bp,
            scheme: bscheme,
        } = right;
        if !self.equal(a, b)? {
            return Ok(false);
        }
        if !self.digest_equal(ad, bd)? {
            return Ok(false);
        }
        if !self.producer_equal(ap.as_ref(), bp.as_ref())? {
            return Ok(false);
        }
        self.admit(2, 0)?;
        Ok(match ascheme {
            trust_ir::imports::IdentityScheme::V2 => {
                matches!(bscheme, trust_ir::imports::IdentityScheme::V2)
            }
            trust_ir::imports::IdentityScheme::V3 => {
                matches!(bscheme, trust_ir::imports::IdentityScheme::V3)
            }
        })
    }
    pub(super) fn digest_equal(
        &mut self,
        left: &trust_ir::ProofDigest,
        right: &trust_ir::ProofDigest,
    ) -> R<bool> {
        self.admit(34, 0)?;
        let trust_ir::ProofDigest {
            algorithm: a,
            bytes: ab,
        } = left;
        let trust_ir::ProofDigest {
            algorithm: b,
            bytes: bb,
        } = right;
        // Explicit fixed array types make a future variable preimage require a
        // new real traversal, instead of silently inheriting this fixed price.
        let (ab, bb): (&[u8; 32], &[u8; 32]) = (ab, bb);
        let algorithm = match a {
            ProofDigestAlgorithm::Sha256 => matches!(b, ProofDigestAlgorithm::Sha256),
            ProofDigestAlgorithm::TrustIrStableV1 => {
                matches!(b, ProofDigestAlgorithm::TrustIrStableV1)
            }
        };
        Ok(algorithm && ab == bb)
    }
    fn producer_equal(&mut self, left: Option<&Producer>, right: Option<&Producer>) -> R<bool> {
        self.admit(8, 2 * size_of::<Option<&Producer>>())?;
        let (left, right) = match (left, right) {
            (None, None) => return Ok(true),
            (Some(a), Some(b)) => (a, b),
            _ => return Ok(false),
        };
        Ok(match left {
            Producer::TRust => matches!(right, Producer::TRust),
            Producer::Clean => matches!(right, Producer::Clean),
            Producer::TrustIr => matches!(right, Producer::TrustIr),
            Producer::TSwift => matches!(right, Producer::TSwift),
            Producer::TC => matches!(right, Producer::TC),
            Producer::Other(a) => match right {
                Producer::Other(b) => self.equal(a, b)?,
                _ => false,
            },
        })
    }
}
