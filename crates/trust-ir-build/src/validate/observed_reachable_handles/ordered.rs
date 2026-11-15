// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn insert<O: ExecutionObserver>(
        &mut self,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<&HandleTy>())?;
        let Ty::Handle(new) = ty else {
            return Err(ObservedValueError::InvalidRange);
        };
        let mut at = 0usize;
        while let Some(old) = work.at(&self.handles, at)? {
            work.admit(1, size_of::<&HandleTy>())?;
            let Ty::Handle(old) = old else {
                return Err(ObservedValueError::InvalidRange);
            };
            let order = work.compare(&old.name, &new.name)?;
            let order = if order == Ordering::Equal {
                work.compare(&old.runtime, &new.runtime)?
            } else {
                order
            };
            match order {
                Ordering::Equal => return Ok(()),
                Ordering::Greater => break,
                Ordering::Less => work.next(&mut at)?,
            }
        }
        // Append then perform only individually admitted fixed pointer swaps.
        // A stop leaves all borrowed rows owned in State, not a partial set.
        work.push(&mut self.handles, ty)?;
        work.admit(1, size_of::<usize>())?;
        let mut end = self.handles.len() - 1;
        loop {
            work.admit(1, 0)?;
            if end == at {
                break;
            }
            work.admit(3, 2 * size_of::<&Ty>() + size_of::<usize>())?;
            self.handles.swap(end, end - 1);
            end -= 1;
        }
        Ok(())
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn compare(&mut self, a: &str, b: &str) -> R<Ordering> {
        self.admit(1, 3 * size_of::<usize>())?;
        let mut at = 0usize;
        let len = a.len().min(b.len());
        loop {
            self.admit(1, 0)?;
            if at == len {
                break;
            }
            let end = at.saturating_add(1024).min(len);
            self.admit(end - at, size_of::<Ordering>())?;
            let order = a.as_bytes()[at..end].cmp(&b.as_bytes()[at..end]);
            if order != Ordering::Equal {
                return Ok(order);
            }
            self.admit(1, size_of::<usize>())?;
            at = end;
        }
        self.admit(1, size_of::<Ordering>())?;
        Ok(a.len().cmp(&b.len()))
    }
}
