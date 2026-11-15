// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Inherited {
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
            let out = &mut self.reason;
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
        mut value: u64,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        // Exact finite u64 decimal primitive, at most20 digits.
        w.admit(1, 20)?;
        let mut digits = [0u8; 20];
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
        w.admit(20, size_of::<&str>())?;
        let text =
            core::str::from_utf8(&digits[at..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.text(text, w)
    }
}

impl Inherited {
    pub(super) fn quoted<O: ExecutionObserver>(
        &mut self,
        mut source: &str,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.text("\"", w)?;
        loop {
            w.admit(4, 2 * size_of::<char>())?;
            let Some(character) = source.chars().next() else {
                break;
            };
            source = &source[character.len_utf8()..];
            if character == '\'' {
                self.text("'", w)?;
                continue;
            }
            // Actual pinned698 Unicode table lemma: each table's full offset
            // scan plus header probes, whitespace256 and scalar guards8*32.
            const TABLE_VISITS: usize = 33 + 767 + 12 + 35 + 11 + 43 + 54 + 1461 + 256;
            w.admit(
                8 * u32::BITS as usize + TABLE_VISITS,
                size_of::<core::char::EscapeDebug>(),
            )?;
            let mut escaped = character.escape_debug();
            loop {
                w.admit(1, size_of::<Option<char>>())?;
                let Some(character) = escaped.next() else {
                    break;
                };
                w.admit(4, 4)?;
                let mut utf8 = [0u8; 4];
                self.text(character.encode_utf8(&mut utf8), w)?;
            }
        }
        self.text("\"", w)
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn inherited_string(&mut self, value: String) {
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
}
