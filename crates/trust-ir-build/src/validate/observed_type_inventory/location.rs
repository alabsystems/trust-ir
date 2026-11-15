// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Clone, Copy)]
pub(super) enum Location<'a> {
    Type(usize),
    Struct(&'a str, usize),
    Record(&'a str, usize),
    Enum(&'a str, &'a str, usize),
    Closure(usize),
    Capture(usize, usize),
    Parameter(usize, usize),
    Return(usize, usize),
    Global(&'a str),
    DropGlue(usize),
    Function(&'a str, u32),
}
impl State<'_> {
    pub(super) fn location<O: ExecutionObserver>(
        &mut self,
        source: Location<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.flat(take(&mut self.location));
        work.admit(11, 2 * size_of::<Location<'_>>())?;
        match source {
            Location::Type(i) => {
                work.text("type.", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
            }
            Location::Struct(name, i) | Location::Record(name, i) => {
                work.text(
                    if matches!(source, Location::Struct(..)) {
                        "struct '"
                    } else {
                        "record '"
                    },
                    &mut self.location,
                )?;
                work.text(name, &mut self.location)?;
                work.text("' field ", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
            }
            Location::Enum(name, variant, i) => {
                work.text("enum '", &mut self.location)?;
                work.text(name, &mut self.location)?;
                work.text("' variant '", &mut self.location)?;
                work.text(variant, &mut self.location)?;
                work.text("' field ", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
            }
            Location::Closure(i) => {
                work.text("closure.", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
            }
            Location::Capture(i, j) => {
                work.text("closure.", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
                work.text(" capture ", &mut self.location)?;
                work.number(j as u128, &mut self.location)?;
            }
            Location::Parameter(i, j) | Location::Return(i, j) => {
                work.text("functy.", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
                work.text(
                    if matches!(source, Location::Parameter(..)) {
                        " param "
                    } else {
                        " return "
                    },
                    &mut self.location,
                )?;
                work.number(j as u128, &mut self.location)?;
            }
            Location::Global(name) => {
                work.text("global '", &mut self.location)?;
                work.text(name, &mut self.location)?;
                work.text("'", &mut self.location)?;
            }
            Location::DropGlue(i) => {
                work.text("drop_glue row ", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
            }
            Location::Function(name, i) => {
                work.text("function '", &mut self.location)?;
                work.text(name, &mut self.location)?;
                work.text("' bb", &mut self.location)?;
                work.number(u128::from(i), &mut self.location)?;
            }
        }
        Ok(())
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn number(&mut self, mut value: u128, out: &mut String) -> R {
        self.admit(40, 40 + 2 * size_of::<usize>())?;
        let mut digits = [0u8; 40];
        let mut begin = digits.len();
        loop {
            self.admit(3, 1)?;
            begin = begin
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            digits[begin] =
                b'0' + u8::try_from(value % 10).map_err(|_| ObservedValueError::InvalidRange)?;
            value /= 10;
            if value == 0 {
                break;
            }
        }
        self.admit(40, size_of::<&str>())?;
        let text =
            core::str::from_utf8(&digits[begin..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.text(text, out)
    }
}
