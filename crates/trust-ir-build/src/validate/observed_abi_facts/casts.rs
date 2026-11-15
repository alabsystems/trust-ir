// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn cast<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        function: &Function,
        ty: &Ty,
        pieces: &[Ty],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, 0)?;
        if pieces.is_empty() {
            w.text("`cast` names no lanes", &mut self.detail)?;
            self.commit(function, w)?;
        }
        let mut i = 0;
        while let Some(piece) = w.at(pieces, i)? {
            w.admit(67, 0)?;
            if !is_closed_scalar_ty(piece) {
                w.text("`cast` lane ", &mut self.detail)?;
                self.text_ty(piece, w)?;
                w.text(" is not a closed scalar", &mut self.detail)?;
                self.commit(function, w)?;
                return Ok(());
            }
            w.next(&mut i)?;
        }
        i = 0;
        while let Some(piece) = w.at(pieces, i)? {
            if self.size(layouts, piece, w)? == Some(0) {
                w.text("`cast` lane ", &mut self.detail)?;
                self.text_ty(piece, w)?;
                w.text(" has no width", &mut self.detail)?;
                self.commit(function, w)?;
                return Ok(());
            }
            w.next(&mut i)?;
        }
        let mut total = Some(0u64);
        i = 0;
        while let Some(piece) = w.at(pieces, i)? {
            // Exact try_fold short-circuit: no later size query after None.
            let size = self.size(layouts, piece, w)?;
            w.admit(2, size_of::<Option<u64>>())?;
            total = match (total, size) {
                (Some(sum), Some(size)) => Some(
                    sum.checked_add(size)
                        .ok_or(ObservedValueError::CapacityOverflow)?,
                ),
                _ => None,
            };
            if total.is_none() {
                break;
            }
            w.next(&mut i)?;
        }
        // The original tuple evaluates the slot layout even if lane sum None.
        let slot = self.size(layouts, ty, w)?;
        w.admit(4, 0)?;
        match (total, slot) {
            (Some(total), Some(size)) if total < size => {
                w.text("`cast` lanes total ", &mut self.detail)?;
                w.unsigned(u128::from(total), &mut self.detail)?;
                w.text(" bytes, which does not cover ", &mut self.detail)?;
                self.text_ty(ty, w)?;
                w.text(" (", &mut self.detail)?;
                w.unsigned(u128::from(size), &mut self.detail)?;
                w.text(" bytes)", &mut self.detail)?;
                self.commit(function, w)?;
            }
            (None, _) | (_, None) => {
                w.text("`cast` needs a computable layout for ", &mut self.detail)?;
                self.text_ty(ty, w)?;
                w.text(" and every lane", &mut self.detail)?;
                self.commit(function, w)?;
            }
            _ => {}
        }
        Ok(())
    }
}
