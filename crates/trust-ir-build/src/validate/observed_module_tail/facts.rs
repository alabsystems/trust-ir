// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::proof::ProofAnnotation;
impl State {
    pub(super) fn facts<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut f = 0;
        while let Some(function) = work.at(&module.functions, f)? {
            self.annotations(function.id.index(), &function.proofs, work)?;
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    self.annotations(function.id.index(), &node.proofs, work)?;
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            work.next(&mut f)?;
        }
        Ok(())
    }
    fn annotations<O: ExecutionObserver>(
        &mut self,
        function: u32,
        annotations: &[ProofAnnotation],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(ann) = work.at(annotations, at)? {
            work.admit(128, size_of::<Option<ValidationError>>())?;
            let error = match ann {
                ProofAnnotation::ValueRange { lo, hi } if lo > hi => {
                    Some(ValidationError::ValueRangeInverted {
                        function,
                        lo: *lo,
                        hi: *hi,
                    })
                }
                ProofAnnotation::KnownBits { zeros, ones } if zeros & ones != 0 => {
                    Some(ValidationError::KnownBitsContradiction {
                        function,
                        overlap: zeros & ones,
                    })
                }
                _ => None,
            };
            if let Some(error) = error {
                // These two exact scalar variants have no owning children. The pending
                // stack row is fixed data; no cloned annotation payload is retained.
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>())?;
                self.errors.push(error);
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
}
