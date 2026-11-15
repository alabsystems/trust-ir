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

    pub(super) fn push<T: Copy>(&mut self, rows: &mut Vec<T>, value: T) -> R {
        self.reserve(rows)?;
        self.admit(1, size_of::<T>())?;
        rows.push(value);
        Ok(())
    }

    pub(super) fn text(&mut self, mut source: &str, output: &mut String) -> R {
        while !source.is_empty() {
            self.admit(1, 0)?;
            let mut end = source.len().min(1024);
            loop {
                self.admit(1, 0)?;
                if source.is_char_boundary(end) {
                    break;
                }
                end -= 1;
            }
            let chunk = &source[..end];
            let needed = output
                .len()
                .checked_add(chunk.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if needed > output.capacity() {
                let requested = output
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(chunk.len()))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let images = requested
                    .checked_add(output.capacity())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                self.admit(images, images)?;
                output
                    .try_reserve_exact(requested - output.len())
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            self.admit(chunk.len(), chunk.len())?;
            output.push_str(chunk);
            source = &source[end..];
        }
        Ok(())
    }

    pub(super) fn number(&mut self, mut value: u128, output: &mut String) -> R {
        // u128 has at most 39 decimal digits; this fixed buffer also covers
        // every u32 block ID and usize index without a narrowing conversion.
        self.admit(40, 40)?;
        let mut digits = [0u8; 40];
        let mut end = digits.len();
        loop {
            self.admit(1, 1)?;
            end = end
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            digits[end] = b'0' + (value % 10) as u8;
            value /= 10;
            if value == 0 {
                break;
            }
        }
        self.admit(digits.len() - end, 0)?;
        let text =
            core::str::from_utf8(&digits[end..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.text(text, output)
    }

    pub(super) fn publication(&mut self, bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: bytes,
            })
            .map_err(Into::into)
    }

    pub(super) fn retire<T>(&mut self, value: T) {
        self.session.retirement_step(self.site, 1);
        drop(value);
        self.session.retirement_poll(self.site);
    }

    pub(super) fn retire_vec<T>(&mut self, rows: &mut Vec<T>) {
        while !rows.is_empty() {
            self.session.retirement_step(self.site, 1);
            let _ = rows.pop();
        }
        self.retire(take(rows));
    }

    pub(super) fn at<'a, T>(&mut self, rows: &'a [T], index: usize) -> R<Option<&'a T>> {
        self.admit(1, size_of::<Option<&T>>())?;
        Ok(rows.get(index))
    }
    pub(super) fn step(&mut self, work: usize) {
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn flat(&mut self, value: String) {
        let mut at = 0;
        while at < value.len() {
            let n = (value.len() - at).min(1024);
            self.step(n);
            at += n;
        }
        self.retire(value);
    }
    pub(super) fn errors(&mut self, rows: &mut Vec<ValidationError>) {
        let _ = retire_validation_errors_observed(take(rows), self.session, self.site);
    }
    pub(super) fn transfer(
        &mut self,
        from: &mut Vec<ValidationError>,
        to: &mut Vec<ValidationError>,
    ) -> R {
        while !from.is_empty() {
            self.reserve(to)?;
            let bytes = from
                .len()
                .checked_mul(size_of::<ValidationError>())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(from.len(), bytes)?;
            // Whole child remains in from until every destination fee succeeds.
            to.push(from.remove(0));
        }
        self.retire_vec(from);
        Ok(())
    }
    pub(super) fn eq_bytes(&mut self, a: &[u8], b: &[u8]) -> R<bool> {
        self.admit(1, 0)?;
        if a.len() != b.len() {
            return Ok(false);
        }
        for i in 0..a.len() {
            self.admit(1, 0)?;
            if a[i] != b[i] {
                return Ok(false);
            }
        }
        Ok(true)
    }
    pub(super) fn signed(&mut self, value: i128, out: &mut String) -> R {
        self.admit(1, 0)?;
        if value < 0 {
            self.text("-", out)?;
        }
        self.number(value.unsigned_abs(), out)
    }
    pub(super) fn ty(&mut self, ty: &Ty, out: &mut String) -> R {
        self.admit(1, size_of::<String>())?;
        let child = ty.display_observed(self.session, self.site)?;
        let result = self.text(&child, out);
        self.flat(child);
        result
    }
    pub(super) fn constant(&mut self, value: &Constant, out: &mut String) -> R {
        self.admit(1, size_of::<String>())?;
        let child = value.display_observed(self.session, self.site)?;
        let result = self.text(&child, out);
        self.flat(child);
        result
    }
    pub(super) fn index(&mut self, index: usize) -> R<u32> {
        self.admit(1, size_of::<u32>())?;
        u32::try_from(index).map_err(|_| ObservedValueError::CapacityOverflow)
    }

    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
