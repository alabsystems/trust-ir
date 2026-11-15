// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn reserve(&mut self, rows: &mut Vec<ValidationError>) -> R {
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
                    .checked_mul(size_of::<ValidationError>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<FunctionValidationReport>(),
            })
            .map_err(Into::into)
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
impl State {
    pub(super) fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        if self.pending.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn merge<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        let start = self.errors.len();
        loop {
            work.admit(1, 0)?;
            if self.pending.is_empty() {
                break;
            }
            // Reserve and price both fixed error-header moves before popping;
            // a refusal keeps every owned payload in one of the two Vecs.
            work.reserve(&mut self.errors)?;
            work.admit(2, 2 * size_of::<ValidationError>())?;
            let error = self.pending.pop().ok_or(ObservedValueError::InvalidRange)?;
            self.errors.push(error);
        }
        self.retire_pending(work);
        work.admit(1, 0)?;
        let mut left = start;
        let mut right = self.errors.len();
        loop {
            work.admit(2, 0)?;
            if right.saturating_sub(left) < 2 {
                return Ok(());
            }
            right = right
                .checked_sub(1)
                .ok_or(ObservedValueError::InvalidRange)?;
            work.admit(1, 3 * size_of::<ValidationError>())?;
            self.errors.swap(left, right);
            left = left
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
