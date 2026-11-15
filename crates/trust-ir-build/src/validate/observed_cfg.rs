// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual switch-key, edge-target and CFG reachability validation.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct Successors {
    block: u32,
    targets: Vec<u32>,
}
#[derive(Default)]
struct Checking<'a> {
    errors: Vec<ValidationError>,
    pending: Option<ValidationError>,
    text: String,
    keys: Vec<String>,
    blocks: Vec<u32>,
    successors: Vec<Successors>,
    targets: Vec<u32>,
    edges: Vec<trust_ir::Edge<'a>>,
    reachable: Vec<u32>,
    queue: Vec<u32>,
}

/// Exact ordinary control-flow diagnostics using this function's actual block
/// IDs, including last-definition successor replacement for duplicate IDs.
/// Switch keys use the actual observed ordinary Constant Display traversal,
/// including exact float spelling and display-key collisions across variants.
/// All work/storage and cleanup use the caller's original session/site. Empty
/// output is this constituent only, not full validation or source/proof authority.
/// Successful diagnostics and original inputs remain caller-owned. Physical
/// allocator/deallocation/panic/unwind/RSS/hard time guarantees are separate.
pub fn validate_function_control_flow_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Checking<'_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = Checking::default();
    let mut work = Work { session, site };
    let result = state.walk(function, &mut work);
    state.retire_scratch(&mut work);
    let result = result.and_then(|()| work.publication());
    match result {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}
impl<'a> Checking<'a> {
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> ValidationError,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Only fixed Copy captures are passed to this private constructor.
        work.admit(1, size_of::<ValidationError>())?;
        self.pending = Some(make());
        self.commit(work)
    }
    fn commit<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        if let Some(error) = self.pending.take() {
            self.errors.push(error);
        }
        Ok(())
    }
    fn switch_keys<O: ExecutionObserver>(
        &mut self,
        block: u32,
        cases: &'a [trust_ir::inst::SwitchCase],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for case in cases {
            work.admit(1, 0)?;
            // Keep the returned owned String immediately, before a later
            // comparison, reserve or diagnostic publication can refuse.
            self.text = case.value.display_observed(work.session, work.site)?;
            let mut duplicate = false;
            for key in &self.keys {
                if work.equal(key, &self.text)? {
                    duplicate = true;
                    break;
                }
            }
            if duplicate {
                work.admit(1, size_of::<ValidationError>())?;
                self.pending = Some(ValidationError::DuplicateSwitchCase {
                    block,
                    value: take(&mut self.text),
                });
                self.commit(work)?;
            } else {
                work.reserve(&mut self.keys)?;
                work.admit(1, size_of::<String>())?;
                self.keys.push(take(&mut self.text));
            }
        }
        self.retire_keys(work);
        // Retirement can itself be the first cancellation point.
        work.admit(1, 0)
    }
    fn store_successors<O: ExecutionObserver>(
        &mut self,
        block: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for row in &mut self.successors {
            work.admit(1, 0)?;
            if row.block == block {
                work.admit(1, size_of::<Vec<u32>>())?;
                let old = core::mem::replace(&mut row.targets, take(&mut self.targets));
                work.retire(old);
                return work.admit(1, 0);
            }
        }
        work.reserve(&mut self.successors)?;
        work.admit(1, size_of::<Successors>())?;
        self.successors.push(Successors {
            block,
            targets: take(&mut self.targets),
        });
        Ok(())
    }
}
