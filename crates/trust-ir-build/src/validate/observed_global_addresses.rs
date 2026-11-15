// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original GlobalAddr row-bound diagnostics, not relocation authority.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
#[cfg(test)]
mod tests;
type R<T = ()> = Result<T, ObservedValueError>;
struct Work<'s, 'o, O: ExecutionObserver> {
    session: &'s mut ObservedSession<'o, O>,
    site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    fn next(&mut self, index: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    fn fixed(&mut self, errors: &mut Vec<ValidationError>, block: u32, global_id: u32) -> R {
        self.admit(1, 0)?;
        if errors.len() == errors.capacity() {
            let requested = errors
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(errors.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<ValidationError>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            errors
                .try_reserve_exact(requested - errors.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        self.admit(1, size_of::<ValidationError>())?;
        errors.push(ValidationError::GlobalNotFound { block, global_id });
        Ok(())
    }
    fn walk(&mut self, module: &Module, errors: &mut Vec<ValidationError>) -> R {
        self.admit(1, size_of::<usize>())?;
        let count = module.globals.len();
        let mut fi = 0usize;
        loop {
            self.admit(1, size_of::<Option<&Function>>())?;
            let Some(function) = module.functions.get(fi) else {
                return Ok(());
            };
            let mut bi = 0usize;
            loop {
                self.admit(1, size_of::<Option<&trust_ir::Block>>())?;
                let Some(block) = function.blocks.get(bi) else {
                    break;
                };
                let mut ni = 0usize;
                loop {
                    self.admit(2, size_of::<Option<&trust_ir::InstrNode>>())?;
                    let Some(node) = block.body.get(ni) else {
                        break;
                    };
                    if let Inst::GlobalAddr { global } = &node.inst
                        && global.as_usize() >= count
                    {
                        self.fixed(errors, block.id.index(), global.index())?;
                    }
                    self.next(&mut ni)?;
                }
                self.next(&mut bi)?;
            }
            self.next(&mut fi)?;
        }
    }
}
/// Visit every physically stored function/block/instruction in original order,
/// including unreachable, duplicate and external rows. A global ID denotes its
/// table index, so the exact original rule compares it to globals.len(), without
/// inspecting names/types/initializers or relying on global-row contents.
/// All actual traversal, error growth and failure retirement use the supplied
/// original session/site; no partial list escapes refusal. This says nothing
/// about relocation, types, source/proof authority or complete module validity.
/// Successful output/input disposal and physical allocator/time remain caller
/// responsibilities. No new owner, grant, deadline, TLS, flag or policy.
pub fn validate_module_global_addresses_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Vec<ValidationError>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut errors = Vec::new();
    let mut work = Work { session, site };
    let result = work.walk(module, &mut errors).and_then(|()| {
        work.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: work.site,
                work: 1,
                copy_bytes: size_of::<Vec<ValidationError>>(),
            })
            .map_err(Into::into)
    });
    match result {
        Ok(()) => Ok(errors),
        Err(error) => {
            let _ = retire_validation_errors_observed(take(&mut errors), work.session, work.site);
            Err(if work.session.first_refusal().is_some() {
                ObservedValueError::AdmissionRefused
            } else {
                error
            })
        }
    }
}
