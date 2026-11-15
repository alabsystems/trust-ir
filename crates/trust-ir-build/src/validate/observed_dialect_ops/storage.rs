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
    pub(super) fn step(&mut self, work: usize) {
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
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
                .checked_add(rows.capacity())
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
    pub(super) fn text(&mut self, mut source: &str, output: &mut String) -> R {
        loop {
            self.admit(1, size_of::<usize>())?;
            if source.is_empty() {
                return Ok(());
            }
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
    }
    pub(super) fn flat(&mut self, text: String) {
        self.step(size_of::<String>().saturating_add(1));
        drop(text);
        self.poll();
    }
    pub(super) fn unsigned(&mut self, mut value: u128, output: &mut String) -> R {
        const DIGITS: [&str; 10] = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"];
        self.admit(
            1,
            size_of::<[u8; 39]>() + size_of::<usize>() + size_of::<u128>(),
        )?;
        let mut digits = [0u8; 39];
        let mut begin = digits.len();
        loop {
            self.admit(
                3,
                2 * size_of::<u128>() + size_of::<usize>() + size_of::<u8>(),
            )?;
            begin = begin
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            digits[begin] = (value % 10) as u8;
            value /= 10;
            if value == 0 {
                break;
            }
        }
        while let Some(digit) = self.at(&digits, begin)? {
            self.admit(1, size_of::<usize>())?;
            let index = usize::from(*digit);
            let text = self
                .at(&DIGITS, index)?
                .ok_or(ObservedValueError::InvalidRange)?;
            self.admit(1, size_of::<&str>())?;
            let text = *text;
            self.text(text, output)?;
            self.next(&mut begin)?;
        }
        Ok(())
    }
    pub(super) fn rows<T: Copy>(&mut self, mut rows: Vec<T>) {
        loop {
            self.step(size_of::<Option<T>>().saturating_add(1));
            if rows.pop().is_none() {
                break;
            }
        }
        self.step(size_of::<Vec<T>>().saturating_add(1));
        drop(rows);
        self.poll();
    }
}

impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn quoted(&mut self, mut source: &str, output: &mut String) -> R {
        self.text("\"", output)?;
        loop {
            // Decoding a single UTF8 scalar is bounded by four source bytes.
            self.admit(4, 2 * size_of::<char>())?;
            let Some(character) = source.chars().next() else {
                break;
            };
            source = &source[character.len_utf8()..];
            if character == '\'' {
                // Debug(str) leaves apostrophes verbatim; char.escape_debug
                // escapes them because its public default also serves chars.
                self.text("'", output)?;
                continue;
            }
            // Scalar Unicode classification is a fixed std primitive, not a
            // string walk. Price eight u32-domain property searches before
            // construction; each escaped scalar then has its own admission.
            // This is logical pricing, never an installed-std/hard-time claim.
            // Exact pinned698 Unicode source: four skip_search tables have
            // (headers,offsets)=(33,767),(12,35),(11,43),(54,1461).
            // Each binary search probes at most its header count, and each
            // forward run reads at most its full offsets array. The 256-byte
            // whitespace table plus 8*u32::BITS cover its fixed cascade and
            // all scalar guards/extra header probes. See STD-BINDINGS and
            // the complete source-derived lemma; no opaque string traversal.
            const UNICODE_TABLE_VISITS: usize = 33 + 767 + 12 + 35 + 11 + 43 + 54 + 1461 + 256;
            self.admit(
                8 * u32::BITS as usize + UNICODE_TABLE_VISITS,
                size_of::<core::char::EscapeDebug>(),
            )?;
            let mut escaped = character.escape_debug();
            loop {
                self.admit(1, size_of::<Option<char>>())?;
                let Some(character) = escaped.next() else {
                    break;
                };
                self.admit(4, 4)?;
                let mut utf8 = [0u8; 4];
                self.text(character.encode_utf8(&mut utf8), output)?;
            }
        }
        self.text("\"", output)
    }
    pub(super) fn eq(&mut self, a: &str, b: &str) -> R<bool> {
        self.admit(1, size_of::<bool>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        let mut at = 0;
        while at < a.len() {
            let end = at
                .checked_add(1024)
                .ok_or(ObservedValueError::CapacityOverflow)?
                .min(a.len());
            self.admit(2 * (end - at), 0)?;
            if a.as_bytes()[at..end] != b.as_bytes()[at..end] {
                return Ok(false);
            }
            at = end;
        }
        Ok(true)
    }
    pub(super) fn attr<'a>(&mut self, op: &'a DialectInst, name: &str) -> R<Option<&'a AttrValue>> {
        let mut at = 0;
        while let Some(a) = self.at(&op.attrs, at)? {
            if self.eq(&a.name, name)? {
                return Ok(Some(&a.value));
            }
            self.next(&mut at)?;
        }
        Ok(None)
    }
}
