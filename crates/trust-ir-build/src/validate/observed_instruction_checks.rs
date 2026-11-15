// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! The actual function walk for alignments and arithmetic annotation conflicts.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
#[cfg(test)]
mod tests;
type R<T = ()> = Result<T, ObservedValueError>;
/// Plain constituent output, with no validator report or source/proof authority.
/// The indirect-call bit retains the classification fused into the original
/// alignment walk. Successful output disposal remains the caller's duty.
#[derive(Debug, Default)]
pub struct ObservedFunctionInstructionChecks {
    pub errors: Vec<ValidationError>,
    pub has_indirect_call: bool,
}
/// Exact original alignment diagnostics, followed by arithmetic annotation
/// conflicts, and the original fused indirect-call classification. Actually
/// observes every visited block/instruction/annotation under the original
/// session/site, without walking variable proof payloads. This runs no other
/// validator or authority check. Physical allocator/panic/time limits and the
/// original input remain caller duties.
pub fn validate_function_instruction_checks_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ObservedFunctionInstructionChecks> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<ObservedFunctionInstructionChecks>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut result = ObservedFunctionInstructionChecks::default();
    let mut work = Work { session, site };
    let checked = result
        .alignments(function, &mut work)
        .and_then(|()| result.annotations(function, &mut work))
        .and_then(|()| {
            work.session
                .admit(ExecutionProgress {
                    phase: ExecutionPhase::Publication,
                    site,
                    work: 1,
                    copy_bytes: size_of::<ObservedFunctionInstructionChecks>(),
                })
                .map_err(Into::into)
        });
    match checked {
        Ok(()) => Ok(result),
        Err(error) => {
            while !result.errors.is_empty() {
                work.session.retirement_step(site, 1);
                // The only produced errors have fixed scalar/static fields.
                result.errors.pop();
            }
            work.session.retirement_step(site, 1);
            drop(take(&mut result.errors));
            work.session.retirement_poll(site);
            Err(if work.session.first_refusal().is_some() {
                ObservedValueError::AdmissionRefused
            } else {
                error
            })
        }
    }
}
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
    fn reserve<T>(&mut self, rows: &mut Vec<T>) -> R {
        self.admit(1, 0)?;
        if rows.len() == rows.capacity() {
            let requested = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(rows.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    fn any(
        &mut self,
        proofs: &[ProofAnnotation],
        matches: impl Fn(&ProofAnnotation) -> bool,
    ) -> R<bool> {
        self.admit(1, 0)?;
        for proof in proofs {
            self.admit(1, 0)?;
            if matches(proof) {
                return Ok(true);
            }
        }
        Ok(false)
    }
}
impl ObservedFunctionInstructionChecks {
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> ValidationError,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Private callers capture only fixed scalar/static fields. Complete
        // admission precedes construction, then Vec::push cannot allocate.
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(make());
        Ok(())
    }
    fn alignments<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            for node in &block.body {
                work.admit(1, 0)?;
                let alignment = match &node.inst {
                    Inst::Load { align, .. } => Some((*align, "load")),
                    Inst::Store { align, .. } => Some((*align, "store")),
                    Inst::Alloca { align, .. } => Some((*align, "alloca")),
                    Inst::HeapAlloc { align, .. } => Some((*align, "heap_alloc")),
                    Inst::CallIndirect { .. }
                    | Inst::CallIndirectCannotUnwind { .. }
                    | Inst::InvokeIndirect { .. } => {
                        self.has_indirect_call = true;
                        None
                    }
                    _ => None,
                };
                if let Some((Some(align), kind)) = alignment {
                    work.admit(1, 0)?;
                    if align == 0 || !align.is_power_of_two() {
                        self.fixed(
                            || ValidationError::AccessAlignInvalid { inst: kind, align },
                            work,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }
    fn annotations<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            for node in &block.body {
                work.admit(1, 0)?;
                let wrapping =
                    work.any(&node.proofs, |p| matches!(p, ProofAnnotation::Wrapping))?;
                // Preserve the original second independent any() even when
                // wrapping is absent; no proof payload is cloned or evaluated.
                let no_overflow = work.any(&node.proofs, |p| {
                    matches!(p, ProofAnnotation::NoOverflow | ProofAnnotation::NoWrap)
                })?;
                if wrapping && no_overflow {
                    self.fixed(
                        || ValidationError::WrappingConflictsWithNoOverflow {
                            block: block.id.index(),
                        },
                        work,
                    )?;
                }
            }
        }
        Ok(())
    }
}
