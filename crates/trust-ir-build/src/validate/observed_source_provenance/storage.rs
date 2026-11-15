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
            self.admit(8 * u32::BITS as usize, size_of::<core::char::EscapeDebug>())?;
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
    pub(super) fn number(&mut self, mut value: u128, output: &mut String) -> R {
        self.admit(40, 40)?;
        let mut digits = [0u8; 40];
        let mut start = digits.len();
        loop {
            self.admit(1, 1)?;
            start -= 1;
            digits[start] = b'0' + (value % 10) as u8;
            value /= 10;
            if value == 0 {
                break;
            }
        }
        self.admit(digits.len() - start, 0)?;
        let text =
            core::str::from_utf8(&digits[start..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.text(text, output)
    }
    pub(super) fn block<'f>(
        &mut self,
        function: &'f Function,
        id: BlockId,
    ) -> R<Option<&'f trust_ir::Block>> {
        let mut index = 0usize;
        loop {
            self.admit(1, size_of::<&trust_ir::Block>())?;
            let Some(block) = function.blocks.get(index) else {
                return Ok(None);
            };
            if block.id == id {
                return Ok(Some(block));
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
    pub(super) fn insert<T: Copy + PartialEq>(&mut self, rows: &mut Vec<T>, value: T) -> R<bool> {
        let mut index = 0usize;
        loop {
            self.admit(2, size_of::<T>())?;
            let Some(old) = rows.get(index) else {
                break;
            };
            if *old == value {
                return Ok(false);
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        self.reserve(rows)?;
        self.admit(1, size_of::<T>())?;
        rows.push(value);
        Ok(true)
    }
    pub(super) fn compare(&mut self, left: &str, right: &str) -> R<core::cmp::Ordering> {
        self.admit(1, 0)?;
        for (a, b) in left
            .as_bytes()
            .chunks(1024)
            .zip(right.as_bytes().chunks(1024))
        {
            self.admit(a.len().min(b.len()), 0)?;
            let order = a.cmp(b);
            if order != core::cmp::Ordering::Equal {
                return Ok(order);
            }
        }
        self.admit(1, 0)?;
        Ok(left.len().cmp(&right.len()))
    }
    pub(super) fn blank(&mut self, mut text: &str) -> R<bool> {
        loop {
            self.admit(4, 0)?;
            let Some(character) = text.chars().next() else {
                return Ok(true);
            };
            text = &text[character.len_utf8()..];
            self.admit(8 * u32::BITS as usize, 0)?;
            if !character.is_whitespace() {
                return Ok(false);
            }
        }
    }
    pub(super) fn rows<T: Copy>(&mut self, rows: &mut Vec<T>) {
        loop {
            self.session
                .retirement_step(self.site, size_of::<T>().saturating_add(1));
            if rows.pop().is_none() {
                break;
            }
        }
        self.flat(take(rows));
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
    pub(super) fn flat<T>(&mut self, value: T) {
        self.session
            .retirement_step(self.site, size_of::<T>().saturating_add(1));
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
