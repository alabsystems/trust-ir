// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Post {
    pub(super) fn bridge<O: ExecutionObserver>(
        &mut self,
        rows: &[IslandTheoremRechecked],
        tv: &[TvRechecked],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(row) = w.at(rows, at)? {
            // Exact installed698 source: lazy initial descent, ascent to the
            // next KV, then descent to its successor leaf are the only three
            // height walks. Each has at most population+1 node positions.
            let cursor_visits = row
                .cited
                .len()
                .checked_add(1)
                .and_then(|n| n.checked_mul(3))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            w.admit(
                cursor_visits,
                size_of::<std::collections::btree_set::Iter<'_, String>>(),
            )?;
            let mut cursor = row.cited.iter();
            loop {
                w.admit(
                    cursor_visits,
                    size_of::<Option<&String>>()
                        + size_of::<std::collections::btree_set::Iter<'_, String>>(),
                )?;
                let Some(constant) = cursor.next() else { break };
                let mut found = false;
                let mut pos = 0;
                while let Some(other) = w.at(tv, pos)? {
                    w.admit(64, size_of::<bool>())?;
                    if let Some((island, name)) = &other.island
                        && *island == row.island
                        && w.text_equal(name, constant)?
                    {
                        found = true;
                        break;
                    }
                    w.next(&mut pos)?;
                }
                if !found {
                    self.text("theorem cites @", w)?;
                    self.text(constant, w)?;
                    self.text(
                        ", whose TV certificate is not bound to island declaration ",
                        w,
                    )?;
                    self.text(constant, w)?;
                    self.text(" in this environment — REJECTED (a theorem about an island constant says nothing about the program unless the emitted function is kernel-TV-certified against that very declaration)", w)?;
                    self.failure(row.obligation, w)?;
                }
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    pub(super) fn names<O: ExecutionObserver>(
        &mut self,
        rows: &[IslandTheoremRechecked],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(row) = w.at(rows, at)? {
            let mut earlier = None;
            let mut pos = 0;
            while pos < at {
                let candidate = w.at(rows, pos)?.ok_or(ObservedValueError::InvalidRange)?;
                if w.text_equal(&candidate.theorem, &row.theorem)? {
                    earlier = Some(candidate);
                    break;
                }
                w.next(&mut pos)?;
            }
            if let Some(first) = earlier {
                w.admit(128, size_of::<bool>())?;
                if first.island != row.island || first.statement != row.statement {
                    self.text("lean.theorem `", w)?;
                    self.text(&row.theorem, w)?;
                    self.text("` is already certified by obligation ", w)?;
                    self.number(first.obligation.index(), w)?;
                    self.text(" as a DIFFERENT theorem (", w)?;
                    self.text(
                        if first.island == row.island {
                            "the same island, another grounded statement"
                        } else {
                            "another island"
                        },
                        w,
                    )?;
                    self.text("): the kernel witness is keyed by theorem name, so one name denotes one theorem in a module — REJECTED", w)?;
                    self.failure(row.obligation, w)?;
                }
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
}
