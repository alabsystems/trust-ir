// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
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
    pub(super) fn terminal_publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
    pub(super) fn at<'a, T>(&mut self, rows: &'a [T], at: usize) -> R<Option<&'a T>> {
        self.admit(1, size_of::<Option<&T>>())?;
        Ok(rows.get(at))
    }
    pub(super) fn next(&mut self, at: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *at = at
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    pub(super) fn reserve<T>(&mut self, rows: &mut Vec<T>) -> R {
        self.admit(1, 0)?;
        if rows.len() == rows.capacity() {
            let wanted = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = wanted
                .checked_add(rows.capacity())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(wanted - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn text_equal(&mut self, a: &str, b: &str) -> R<bool> {
        self.admit(2, size_of::<bool>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        let mut at = 0;
        while at < a.len() {
            self.admit(1, size_of::<usize>())?;
            let count = (a.len() - at).min(1024);
            self.admit(
                count
                    .checked_mul(2)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                0,
            )?;
            let end = at
                .checked_add(count)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if a.as_bytes()[at..end] != b.as_bytes()[at..end] {
                return Ok(false);
            }
            at = end;
        }
        Ok(true)
    }
    pub(super) fn step(&mut self, n: usize) {
        self.session.retirement_step(self.site, n);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn terminal(&self, e: ObservedValueError) -> ObservedValueError {
        // The actual local result was held before consuming cleanup. Keep it;
        // the original observer first cause remains separately immutable.
        e
    }
}
