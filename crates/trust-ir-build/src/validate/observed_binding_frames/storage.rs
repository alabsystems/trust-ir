// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn resize<T: Copy>(&mut self, rows: &mut Vec<T>, len: usize, value: T) -> R {
        self.admit(1, 0)?;
        if len > rows.capacity() {
            let images = len
                .checked_add(rows.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(len - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        self.admit(
            len,
            len.checked_mul(size_of::<T>())
                .ok_or(ObservedValueError::CapacityOverflow)?,
        )?;
        rows.resize(len, value);
        Ok(())
    }
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
    pub(super) fn get<T: Copy>(&mut self, rows: &[(u32, T)], key: u32) -> R<Option<T>> {
        self.admit(1, 2 * size_of::<usize>())?;
        let (mut lo, mut hi) = (0, rows.len());
        while lo < hi {
            self.admit(3, size_of::<(u32, T)>() + size_of::<usize>())?;
            let mid = lo + (hi - lo) / 2;
            let (row, value) = rows.get(mid).ok_or(ObservedValueError::InvalidRange)?;
            if *row == key {
                return Ok(Some(*value));
            }
            if *row > key {
                hi = mid;
            } else {
                lo = mid
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
        }
        Ok(None)
    }
    pub(super) fn set<T: Copy>(&mut self, rows: &mut Vec<(u32, T)>, key: u32, value: T) -> R<bool> {
        let mut position = 0;
        loop {
            self.admit(1, size_of::<u32>())?;
            let Some((candidate, _)) = rows.get(position) else {
                break;
            };
            if *candidate == key {
                self.admit(1, size_of::<T>())?;
                rows[position].1 = value;
                return Ok(false);
            }
            if *candidate > key {
                break;
            }
            position = position
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        self.reserve(rows)?;
        self.admit(1, size_of::<(u32, T)>())?;
        rows.push((key, value));
        let mut index = rows.len() - 1;
        while index > position {
            self.admit(1, 2 * size_of::<(u32, T)>())?;
            rows.swap(index - 1, index);
            index -= 1;
        }
        Ok(true)
    }
    pub(super) fn increment(&mut self, rows: &mut Vec<(u32, u32)>, key: u32) -> R {
        let old = self.get(rows, key)?.unwrap_or(0);
        let next = old
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.set(rows, key, next)?;
        Ok(())
    }
    pub(super) fn drain<T: Copy>(&mut self, rows: &mut Vec<T>) {
        while !rows.is_empty() {
            self.session.retirement_step(self.site, 1);
            rows.pop();
        }
        self.flat(take(rows));
    }
    pub(super) fn retire_type(&mut self, ty: &mut Option<Ty>) {
        self.session.retirement_step(self.site, 1);
        if let Some(ty) = ty.take() {
            let _ = ty.retire_observed(self.session, self.site);
        }
        self.session.retirement_poll(self.site);
    }
    pub(super) fn flat<T>(&mut self, value: T) {
        self.session.retirement_step(self.site, 1);
        drop(value);
        self.session.retirement_poll(self.site);
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
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
