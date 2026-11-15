// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<Option<&Function>>())?;
            let Some(function) = module.functions.get(index) else {
                return Ok(());
            };
            if work.synthetic(&function.name)? {
                self.synthetic(function, work)?;
            }
            let mut earlier = 0usize;
            loop {
                work.admit(2, size_of::<Option<&Function>>())?;
                if earlier == index {
                    break;
                }
                let first = module
                    .functions
                    .get(earlier)
                    .ok_or(ObservedValueError::InvalidRange)?;
                if work.equal(&first.name, &function.name)? {
                    self.duplicate(first, function, work)?;
                    break;
                }
                work.next(&mut earlier)?;
            }
            work.next(&mut index)?;
        }
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn synthetic(&mut self, name: &str) -> R<bool> {
        self.admit(2, 2 * size_of::<&[u8]>())?;
        let needle = SYNTHETIC_SYMBOL_MARKER.as_bytes();
        let bytes = name.as_bytes();
        if needle.is_empty() {
            return Ok(true);
        }
        let Some(last) = bytes.len().checked_sub(needle.len()) else {
            return Ok(false);
        };
        let mut index = 0usize;
        loop {
            self.admit(1, 0)?;
            if index > last {
                return Ok(false);
            }
            // The current marker is a fixed13-byte ASCII literal. Byte-window
            // matches are exactly str::contains for this ASCII substring,
            // including names with arbitrary valid UTF8 around the marker.
            self.admit(needle.len(), 0)?;
            let end = index
                .checked_add(needle.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let window = bytes
                .get(index..end)
                .ok_or(ObservedValueError::InvalidRange)?;
            if window == needle {
                return Ok(true);
            }
            self.next(&mut index)?;
        }
    }
}
