// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn algorithm(&mut self, algorithm: ProofDigestAlgorithm, output: &mut String) -> R {
        self.admit(2, 0)?;
        self.text(
            match algorithm {
                ProofDigestAlgorithm::Sha256 => "sha256",
                ProofDigestAlgorithm::TrustIrStableV1 => "trust_ir-stable-v1",
            },
            output,
        )
    }
    pub(super) fn digest(&mut self, digest: &trust_ir::ProofDigest, output: &mut String) -> R {
        self.algorithm(digest.algorithm, output)?;
        self.text(":", output)?;
        for byte in &digest.bytes {
            self.admit(4, 2)?;
            let digits = b"0123456789abcdef";
            let pair = [
                digits[usize::from(byte >> 4)],
                digits[usize::from(byte & 15)],
            ];
            let text = core::str::from_utf8(&pair).map_err(|_| ObservedValueError::InvalidRange)?;
            self.text(text, output)?;
        }
        Ok(())
    }
    pub(super) fn source_place(&mut self, place: SourcePlace, output: &mut String) -> R {
        self.admit(2, 0)?;
        let (name, index) = match place {
            SourcePlace::FunctionParameter { index } => ("FunctionParameter", index),
            SourcePlace::LoopParameter { index } => ("LoopParameter", index),
        };
        self.text(name, output)?;
        self.text(" { index: ", output)?;
        self.number(u128::from(index), output)?;
        self.text(" }", output)
    }
    pub(super) fn scoped_place(&mut self, place: Place, output: &mut String) -> R {
        self.text("(", output)?;
        self.number(u128::from(place.0), output)?;
        self.text(", ", output)?;
        self.number(u128::from(place.1), output)?;
        self.text(", ", output)?;
        self.number(u128::from(place.2), output)?;
        self.text(")", output)
    }
}
