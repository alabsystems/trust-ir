// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Private proof currencies and exact ordinary consumers; replay builder pending.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::proof::{
    ObligationSite, ProofAnnotation, ProofCertificateRef, ProofObligation, ProofStatus,
};
use trust_ir::value::ProofId;
// Expand preparation BEFORE constructing the complete fixed-field error.
// This is closed source syntax, not a caller-provided acceptance callback.
macro_rules! fixed_error {
    ($state:expr,$work:expr,$error:expr) => {{
        $state.prepare($work)?;
        $state.errors.push($error);
        Ok::<(), ObservedValueError>(())
    }};
}
mod bindings;
mod consumers;
mod contexts;
#[cfg(test)]
mod error_precedence_tests;
mod inherited;
mod local;
mod lookup;
mod postchecks;
mod references;
mod storage;
#[cfg(test)]
mod tests;
mod unbound;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
/// Only the completed in-process replay builder in this module may construct
/// these currencies. No public/crate constructor accepts candidate refs or a
/// status/flag/hash/callback. Kernel refs and Discharged-only refs never merge.
/// This private data type and its consumers alone establish NO authority.
struct Authority<'m> {
    module: &'m Module,
    kernel: Vec<ProofCertificateRef>,
    discharged: Vec<ProofCertificateRef>,
}
#[derive(Clone, Copy)]
enum Currency {
    Kernel,
    Discharged,
}
#[derive(Default)]
struct State {
    errors: Vec<ValidationError>,
    candidate: Option<ProofCertificateRef>,
}
impl Authority<'_> {
    fn source<O: ExecutionObserver>(&self, module: &Module, w: &mut Work<'_, '_, O>) -> R {
        w.admit(8, size_of::<bool>())?;
        if !core::ptr::eq(self.module, module) {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn retire<O: ExecutionObserver>(self, w: &mut Work<'_, '_, O>) -> R {
        w.step(
            size_of::<Self>()
                .saturating_add(2 * size_of::<Vec<ProofCertificateRef>>())
                .saturating_add(1),
        );
        for mut rows in [self.kernel, self.discharged] {
            loop {
                w.step(size_of::<Option<ProofCertificateRef>>().saturating_add(1));
                let Some(row) = rows.pop() else { break };
                let _ = row.retire_observed(w.session, w.site);
            }
            w.step(size_of::<Vec<ProofCertificateRef>>().saturating_add(1));
            drop(rows);
            w.poll();
        }
        w.terminal_publication()
    }
}
impl State {
    fn prepare<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<ValidationError>())
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        w: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_candidate(w);
        match result.and_then(|()| w.publication()) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                let _ =
                    retire_validation_errors_observed(take(&mut self.errors), w.session, w.site);
                Err(w.terminal(error))
            }
        }
    }
    fn retire_candidate<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.step(size_of::<Option<ProofCertificateRef>>().saturating_add(1));
        if let Some(value) = self.candidate.take() {
            let _ = value.retire_observed(w.session, w.site);
        }
        w.poll();
    }
}
