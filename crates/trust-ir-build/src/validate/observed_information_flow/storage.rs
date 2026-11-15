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

    pub(super) fn reserve<T>(&mut self, rows: &mut Vec<T>) -> R {
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

    pub(super) fn contains(&mut self, rows: &[u32], value: u32) -> R<bool> {
        self.admit(1, 0)?;
        let mut index = 0;
        while index < rows.len() {
            self.admit(1, 0)?;
            if rows[index] == value {
                return Ok(true);
            }
            index += 1;
        }
        Ok(false)
    }

    pub(super) fn insert(&mut self, rows: &mut Vec<u32>, value: u32) -> R<bool> {
        if self.contains(rows, value)? {
            return Ok(false);
        }
        self.reserve(rows)?;
        self.admit(1, size_of::<u32>())?;
        rows.push(value);
        Ok(true)
    }

    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<Vec<ValidationError>>(),
            })
            .map_err(Into::into)
    }

    pub(super) fn retire<T>(&mut self, value: T) {
        self.session.retirement_step(self.site, 1);
        drop(value);
        self.session.retirement_poll(self.site);
    }

    // Callers supply fixed Copy IDs only; no recursive owned payload is hidden
    // in this generic drain. Poll before each pop and after final deallocation.
    pub(super) fn retire_ids<T: Copy>(&mut self, rows: &mut Vec<T>) {
        while !rows.is_empty() {
            self.session.retirement_step(self.site, 1);
            let _ = rows.pop();
        }
        self.retire(take(rows));
    }

    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
