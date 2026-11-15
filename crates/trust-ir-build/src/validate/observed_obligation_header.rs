// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! First two original proof-integrity groups: IDs, then pinned namespaces.
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
use trust_ir::proof::ObligationKind;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    namespace: String,
    name: String,
    errors: Vec<ValidationError>,
}
/// Preserve every duplicate ID after its first physical row, then reject each
/// Custom namespace absent from the exact existing source-owned admission list.
/// Concrete borrowed scans replace the discarded ID set; exact membership is
/// observed inside the real list/string work. This is a diagnostic prefix of
/// proof integrity, never evidence/authority or a complete integrity verdict.
pub(crate) fn validate_module_proof_obligation_header_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
    work.flat(take(&mut state.namespace));
    work.flat(take(&mut state.name));
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        let mut at = 0usize;
        while let Some(row) = work.at(&module.proof_obligations, at)? {
            let mut earlier = 0usize;
            while earlier < at {
                let previous = work
                    .at(&module.proof_obligations, earlier)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                work.admit(1, 2 * size_of::<u32>())?;
                if previous.id == row.id {
                    self.prepare(work)?;
                    self.errors
                        .push(ValidationError::DuplicateProofObligationId(row.id.index()));
                    break;
                }
                work.next(&mut earlier)?;
            }
            work.next(&mut at)?;
        }
        let mut at = 0usize;
        while let Some(row) = work.at(&module.proof_obligations, at)? {
            work.admit(16, size_of::<Option<(&str, &str)>>())?;
            if let ObligationKind::Custom { namespace, name } = &row.kind
                && !work.namespace(namespace)?
            {
                self.unpinned(row.id.index(), namespace, name, work)?;
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn prepare<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())
    }
    fn unpinned<O: ExecutionObserver>(
        &mut self,
        obligation: u32,
        namespace: &str,
        name: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(namespace, &mut self.namespace)?;
        work.text(name, &mut self.name)?;
        self.prepare(work)?;
        self.errors
            .push(ValidationError::UnpinnedCustomObligationNamespace {
                obligation,
                namespace: take(&mut self.namespace),
                name: take(&mut self.name),
            });
        Ok(())
    }
}
// Formula-text integrity, source/public identity and certificates remain the
// later original groups, in that order. Full module/proof/source/native authority
// and successful caller/input disposal remain OPEN. Logical pricing is not a
// physical allocator/deallocator/OOM/panic/unwind/RSS/hardtime guarantee. No
// owner/grant/deadline/TLS/fuel creation or renewal.
