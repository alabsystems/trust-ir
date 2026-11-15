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
    pub(super) fn publication(&mut self, bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: usize::from(bytes != 0),
                copy_bytes: bytes,
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
    pub(super) fn equal(&mut self, a: &str, b: &str) -> R<bool> {
        self.admit(2, size_of::<bool>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        let (mut at, a, b) = (0, a.as_bytes(), b.as_bytes());
        loop {
            self.admit(1, size_of::<usize>())?;
            if at == a.len() {
                return Ok(true);
            }
            let end = at
                .checked_add((a.len() - at).min(1024))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(end - at, end - at)?;
            if a[at..end] != b[at..end] {
                return Ok(false);
            }
            at = end;
        }
    }
    pub(super) fn count(&mut self, count: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *count = count
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
}
