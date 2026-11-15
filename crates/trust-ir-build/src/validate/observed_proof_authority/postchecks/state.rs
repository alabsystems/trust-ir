// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Default)]
pub(super) struct Post {
    pub(super) errors: Vec<ValidationError>,
    pub(super) scratch: Scratch,
}
impl Post {
    pub(super) fn text<O: ExecutionObserver>(
        &mut self,
        mut text: &str,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        loop {
            w.admit(1, size_of::<usize>())?;
            if text.is_empty() {
                return Ok(());
            }
            let mut n = text.len().min(1024);
            loop {
                w.admit(1, 0)?;
                if text.is_char_boundary(n) {
                    break;
                }
                n -= 1;
            }
            let out = &mut self.scratch.reason;
            w.admit(3, 3 * size_of::<usize>())?;
            let needed = out
                .len()
                .checked_add(n)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if needed > out.capacity() {
                let wanted = out
                    .len()
                    .checked_mul(2)
                    .and_then(|v| v.checked_add(n))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let images = wanted
                    .checked_add(out.capacity())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                w.admit(images, images)?;
                out.try_reserve_exact(wanted - out.len())
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            w.admit(n, n)?;
            out.push_str(&text[..n]);
            text = &text[n..];
        }
    }
    pub(super) fn number<O: ExecutionObserver>(
        &mut self,
        mut value: u32,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        // u32 has at most ten decimal digits; one paid division/remainder per digit.
        w.admit(1, 10)?;
        let mut digits = [0u8; 10];
        let mut at = digits.len();
        loop {
            w.admit(4, 2 * size_of::<usize>() + 1)?;
            at -= 1;
            digits[at] = b'0' + (value % 10) as u8;
            value /= 10;
            if value == 0 {
                break;
            }
        }
        w.admit(10, size_of::<&str>())?;
        let text =
            core::str::from_utf8(&digits[at..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.text(text, w)
    }
    pub(super) fn failure<O: ExecutionObserver>(
        &mut self,
        id: ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<ValidationError>() + size_of::<String>())?;
        self.errors
            .push(ValidationError::CertifiedCleanCicKernelRecheckFailed {
                obligation: id.index(),
                reason: take(&mut self.scratch.reason),
            });
        Ok(())
    }
    pub(super) fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        w: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(w);
        match result.and_then(|()| w.publication()) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                let _ =
                    retire_validation_errors_observed(take(&mut self.errors), w.session, w.site);
                Err(w.terminal(error))
            }
        }
    }
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.step(size_of::<Scratch>() + 1);
        w.string(take(&mut self.scratch.reason));
        w.rows(take(&mut self.scratch.edges));
        w.rows(take(&mut self.scratch.named));
        w.rows(take(&mut self.scratch.parents));
        w.rows(take(&mut self.scratch.queue));
        w.rows(take(&mut self.scratch.path));
        loop {
            w.step(size_of::<Option<Content>>() + 1);
            let Some(group) = self.scratch.content.pop() else {
                break;
            };
            w.bytes(group.bytes);
            w.rows(group.ids);
            w.poll();
        }
        w.step(
            self.scratch
                .content
                .capacity()
                .saturating_mul(size_of::<Content>())
                .saturating_add(size_of::<Vec<Content>>()),
        );
        drop(take(&mut self.scratch.content));
        w.step(size_of::<Option<Vec<u8>>>() + 1);
        if let Some(bytes) = self.scratch.pending_content.take() {
            w.bytes(bytes);
        }
        w.poll();
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn push<T>(&mut self, out: &mut Vec<T>, value: T) -> R
    where
        T: Copy,
    {
        self.reserve(out)?;
        self.admit(1, size_of::<T>())?;
        out.push(value);
        Ok(())
    }
    pub(super) fn rows<T: Copy>(&mut self, mut rows: Vec<T>) {
        loop {
            self.step(size_of::<Option<T>>().saturating_add(1));
            if rows.pop().is_none() {
                break;
            }
        }
        self.step(
            rows.capacity()
                .saturating_mul(size_of::<T>())
                .saturating_add(size_of::<Vec<T>>()),
        );
        drop(rows);
        self.poll();
    }
    pub(super) fn string(&mut self, value: String) {
        self.step(
            value
                .len()
                .saturating_add(value.capacity())
                .saturating_add(size_of::<String>())
                .saturating_add(1),
        );
        drop(value);
        self.poll();
    }
    pub(super) fn bytes(&mut self, mut value: Vec<u8>) {
        while !value.is_empty() {
            let count = value.len().min(1024);
            self.step(count.saturating_add(1));
            value.truncate(value.len() - count);
            self.poll();
        }
        self.step(value.capacity().saturating_add(size_of::<Vec<u8>>()));
        drop(value);
        self.poll();
    }
}
