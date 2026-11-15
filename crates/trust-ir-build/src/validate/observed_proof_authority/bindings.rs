// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original certificate-binding diagnostics; never replay or authority.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::proof::{CertificateBinding, ProofDigest, ProofDigestAlgorithm};
mod fields;
#[cfg(test)]
mod tests;
mod text;
#[derive(Default)]
struct Binding {
    errors: Vec<ValidationError>,
    reason: String,
    field: String,
}
pub(super) fn binding_errors<O: ExecutionObserver>(
    module: &Module,
    row: &ProofObligation,
    binding: &CertificateBinding,
    environment: Option<ProofDigest>,
    statement: Option<ProofDigest>,
    callees: &[String],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut w = Work { session, site };
    w.admit(1, size_of::<Binding>())?;
    let mut state = Binding::default();
    let result = state.run(
        module,
        row,
        binding,
        environment,
        statement,
        callees,
        &mut w,
    );
    state.retire_scratch(&mut w);
    match result.and_then(|()| w.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
            Err(w.terminal(error))
        }
    }
}
impl Binding {
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        row: &ProofObligation,
        binding: &CertificateBinding,
        environment: Option<ProofDigest>,
        statement: Option<ProofDigest>,
        callees: &[String],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(128, 4 * size_of::<Option<ProofDigest>>())?;
        match environment {
            None => {
                self.text("the re-check states no environment digest, so a bound certificate cannot be admitted",w)?;
                self.mismatch(row, "environment_digest", w)?;
            }
            Some(expected) if expected != binding.environment_digest => {
                self.text("certificate claims ", w)?;
                self.digest(binding.environment_digest, w)?;
                self.text(", the environment this re-check built digests to ", w)?;
                self.digest(expected, w)?;
                self.mismatch(row, "environment_digest", w)?;
            }
            Some(_) => {}
        }
        w.admit(128, 4 * size_of::<Option<ProofDigest>>())?;
        match statement {
            None => {
                self.text("the re-check derives no statement digest, so a bound certificate cannot be admitted",w)?;
                self.mismatch(row, "statement_digest", w)?;
            }
            Some(expected) if expected != binding.statement_digest => {
                self.text("certificate claims ", w)?;
                self.digest(binding.statement_digest, w)?;
                self.text(", the statement this re-check derived digests to ", w)?;
                self.digest(expected, w)?;
                self.mismatch(row, "statement_digest", w)?;
            }
            Some(_) => {}
        }
        w.admit(1, size_of::<Option<ProofDigest>>())?;
        if let Some(origin) = binding.origin_module {
            let mut at = 0;
            let mut found = false;
            while let Some(import) = w.at(&module.imports, at)? {
                w.admit(64, 2 * size_of::<ProofDigest>() + size_of::<bool>())?;
                if import.digest == origin {
                    found = true;
                    break;
                }
                w.next(&mut at)?;
            }
            if !found {
                self.text("certificate claims to have been minted in module ", w)?;
                self.digest(origin, w)?;
                self.text(", which no row of `Module::imports` declares", w)?;
                self.mismatch(row, "origin_module", w)?;
            }
        }
        if !self.callees_equal(&binding.callees, callees, w)? {
            self.text("certificate lists callee symbols ", w)?;
            self.strings(&binding.callees, w)?;
            self.text(", the re-derived statement quantifies over ", w)?;
            self.strings(callees, w)?;
            self.mismatch(row, "callees", w)?;
        }
        Ok(())
    }
    fn mismatch<O: ExecutionObserver>(
        &mut self,
        row: &ProofObligation,
        field: &'static str,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        // Only the four fixed ASCII source literals above reach this function.
        w.admit(
            field.len(),
            field
                .len()
                .checked_add(size_of::<String>())
                .ok_or(ObservedValueError::CapacityOverflow)?,
        )?;
        self.field
            .try_reserve_exact(field.len())
            .map_err(|_| ObservedValueError::AllocationFailed)?;
        w.admit(field.len(), field.len())?;
        self.field.push_str(field);
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors
            .push(ValidationError::CertificateBindingMismatch {
                obligation: row.id.index(),
                field: take(&mut self.field),
                detail: take(&mut self.reason),
            });
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.binding_string(take(&mut self.reason));
        w.binding_string(take(&mut self.field));
    }
}
