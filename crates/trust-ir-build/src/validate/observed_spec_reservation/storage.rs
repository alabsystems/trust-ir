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
    pub(super) fn at<'a, T>(&mut self, rows: &'a [T], index: usize) -> R<Option<&'a T>> {
        self.admit(1, size_of::<Option<&T>>())?;
        Ok(rows.get(index))
    }
    pub(super) fn next(&mut self, index: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
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
                    .checked_add(output.len())
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
    pub(super) fn number(&mut self, mut value: u128, out: &mut String) -> R {
        self.admit(40, 40)?;
        let mut digits = [0u8; 40];
        let mut start = digits.len();
        loop {
            self.admit(1, 1)?;
            start = start
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            digits[start] = b'0' + (value % 10) as u8;
            value /= 10;
            if value == 0 {
                break;
            }
        }
        self.admit(digits.len() - start, 0)?;
        let text =
            core::str::from_utf8(&digits[start..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.text(text, out)
    }
    pub(super) fn trim<'a>(&mut self, mut text: &'a str) -> R<&'a str> {
        loop {
            self.admit(8, size_of::<Option<char>>())?;
            let Some(c) = text.chars().next() else {
                return Ok(text);
            };
            if !c.is_whitespace() {
                break;
            }
            text = &text[c.len_utf8()..];
        }
        loop {
            self.admit(8, size_of::<Option<char>>())?;
            let Some(c) = text.chars().next_back() else {
                return Ok(text);
            };
            if !c.is_whitespace() {
                break;
            }
            text = &text[..text.len() - c.len_utf8()];
        }
        Ok(text)
    }
    pub(super) fn equal(&mut self, left: &str, right: &str) -> R<bool> {
        self.admit(1, 2 * size_of::<usize>())?;
        if left.len() != right.len() {
            return Ok(false);
        }
        let mut index = 0;
        while let Some(a) = self.at(left.as_bytes(), index)? {
            let b = self
                .at(right.as_bytes(), index)?
                .ok_or(ObservedValueError::InvalidRange)?;
            self.admit(1, 2)?;
            if a != b {
                return Ok(false);
            }
            self.next(&mut index)?;
        }
        Ok(true)
    }
    pub(super) fn prefix(&mut self, text: &str, prefix: &str, case: Case) -> R<bool> {
        self.admit(1, size_of::<Option<&[u8]>>())?;
        let Some(head) = text.as_bytes().get(..prefix.len()) else {
            return Ok(false);
        };
        let mut index = 0;
        while let Some(a) = self.at(head, index)? {
            let b = self
                .at(prefix.as_bytes(), index)?
                .ok_or(ObservedValueError::InvalidRange)?;
            self.admit(2, 2)?;
            let equal = if matches!(case, Case::AsciiInsensitive) {
                a.eq_ignore_ascii_case(b)
            } else {
                a == b
            };
            if !equal {
                return Ok(false);
            }
            self.next(&mut index)?;
        }
        Ok(true)
    }
    pub(super) fn decimal_index(&mut self, digits: &str) -> R<Option<u32>> {
        self.admit(1, 0)?;
        if digits.is_empty() {
            return Ok(None);
        }
        let mut index = 0;
        while let Some(byte) = self.at(digits.as_bytes(), index)? {
            self.admit(1, 1)?;
            if !byte.is_ascii_digit() {
                return Ok(None);
            }
            self.next(&mut index)?;
        }
        self.admit(2, 0)?;
        if digits.len() > 1 && digits.as_bytes()[0] == b'0' {
            return Ok(None);
        }
        self.admit(1, size_of::<u32>())?;
        let mut value = 0u32;
        let mut index = 0;
        while let Some(byte) = self.at(digits.as_bytes(), index)? {
            self.admit(3, size_of::<Option<u32>>())?;
            let Some(next) = value
                .checked_mul(10)
                .and_then(|n| n.checked_add(u32::from(*byte - b'0')))
            else {
                return Ok(None);
            };
            value = next;
            self.next(&mut index)?;
        }
        Ok(Some(value))
    }
    pub(super) fn quoted(&mut self, mut text: &str, out: &mut String) -> R {
        self.text("\"", out)?;
        loop {
            self.admit(4, 2 * size_of::<char>())?;
            let Some(c) = text.chars().next() else {
                break;
            };
            text = &text[c.len_utf8()..];
            if c == '\'' {
                self.text("'", out)?;
                continue;
            }
            // Same fixed scalar EscapeDebug primitive boundary as TypeDisplay;
            // no physical standard-library or hard-time bound is claimed.
            self.admit(8 * u32::BITS as usize, size_of::<core::char::EscapeDebug>())?;
            let mut escaped = c.escape_debug();
            loop {
                self.admit(1, size_of::<Option<char>>())?;
                let Some(c) = escaped.next() else {
                    break;
                };
                self.admit(4, 4)?;
                let mut utf8 = [0u8; 4];
                self.text(c.encode_utf8(&mut utf8), out)?;
            }
        }
        self.text("\"", out)
    }
    pub(super) fn step(&mut self, n: usize) {
        self.session.retirement_step(self.site, n);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn retire_text(&mut self, text: &mut String) {
        // Logical custody pricing, not a physical allocator/deallocator bound.
        self.session.retirement_step(
            self.site,
            text.len()
                .saturating_add(size_of::<String>())
                .saturating_add(1),
        );
        drop(take(text));
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
