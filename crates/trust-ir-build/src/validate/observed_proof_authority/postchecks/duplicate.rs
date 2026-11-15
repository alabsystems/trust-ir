// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::cmp::Ordering;
impl Post {
    pub(super) fn duplicates<O: ExecutionObserver>(
        &mut self,
        rows: &[&ProofObligation],
        catalog: &ModuleFunctionCatalog<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(row) = w.at(rows, at)? {
            w.admit(1, size_of::<Option<Vec<u8>>>())?;
            self.scratch.pending_content =
                row.clean_cic_lineage_content_v8_observed(catalog, w.session, w.site)?;
            if self.scratch.pending_content.is_some() {
                self.group(row, w)?;
            }
            w.next(&mut at)?;
        }
        let mut at = 0;
        while let Some(group) = w.at(&self.scratch.content, at)? {
            w.admit(1, size_of::<bool>())?;
            if group.ids.len() > 1 {
                w.reserve(&mut self.errors)?;
                w.admit(1, size_of::<ValidationError>() + size_of::<Vec<u32>>())?;
                let group = self
                    .scratch
                    .content
                    .get_mut(at)
                    .ok_or(ObservedValueError::InvalidRange)?;
                self.errors
                    .push(ValidationError::DuplicateObligationContent {
                        function: group.scope,
                        obligations: take(&mut group.ids),
                    });
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn group<O: ExecutionObserver>(&mut self, row: &ProofObligation, w: &mut Work<'_, '_, O>) -> R {
        w.admit(2, size_of::<u32>() + size_of::<Option<usize>>())?;
        let scope = row.function.map_or(u32::MAX, FuncId::index);
        let mut at = 0;
        let mut found = false;
        while let Some(group) = w.at(&self.scratch.content, at)? {
            w.admit(1, size_of::<Ordering>())?;
            let order = scope.cmp(&group.scope);
            let order = if order == Ordering::Equal {
                let bytes = self
                    .scratch
                    .pending_content
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?;
                compare(bytes, &group.bytes, w)?
            } else {
                order
            };
            if order != Ordering::Greater {
                found = order == Ordering::Equal;
                break;
            }
            w.next(&mut at)?;
        }
        if !found {
            w.reserve(&mut self.scratch.content)?;
            let moved = self
                .scratch
                .content
                .len()
                .checked_sub(at)
                .and_then(|v| v.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            w.admit(
                moved,
                moved
                    .checked_mul(size_of::<Content>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            let bytes = self
                .scratch
                .pending_content
                .take()
                .ok_or(ObservedValueError::InvalidRange)?;
            self.scratch.content.insert(
                at,
                Content {
                    scope,
                    bytes,
                    ids: Vec::new(),
                },
            );
        } else {
            w.step(size_of::<Option<Vec<u8>>>() + 1);
            if let Some(bytes) = self.scratch.pending_content.take() {
                w.bytes(bytes);
            }
        }
        w.admit(1, size_of::<&mut Content>())?;
        let group = self
            .scratch
            .content
            .get_mut(at)
            .ok_or(ObservedValueError::InvalidRange)?;
        w.reserve(&mut group.ids)?;
        let mut pos = 0;
        while let Some(other) = w.at(&group.ids, pos)? {
            w.admit(1, size_of::<bool>())?;
            if row.id.index() <= *other {
                break;
            }
            w.next(&mut pos)?;
        }
        let moved = group
            .ids
            .len()
            .checked_sub(pos)
            .and_then(|v| v.checked_add(1))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        w.admit(
            moved,
            moved
                .checked_mul(size_of::<u32>())
                .ok_or(ObservedValueError::CapacityOverflow)?,
        )?;
        group.ids.insert(pos, row.id.index());
        Ok(())
    }
}
fn compare<O: ExecutionObserver>(a: &[u8], b: &[u8], w: &mut Work<'_, '_, O>) -> R<Ordering> {
    let mut at = 0;
    loop {
        w.admit(2, 2 * size_of::<Option<&u8>>())?;
        match (a.get(at), b.get(at)) {
            (Some(a), Some(b)) => {
                w.admit(1, size_of::<Ordering>())?;
                let order = a.cmp(b);
                if order != Ordering::Equal {
                    return Ok(order);
                }
            }
            (None, None) => return Ok(Ordering::Equal),
            (None, Some(_)) => return Ok(Ordering::Less),
            (Some(_), None) => return Ok(Ordering::Greater),
        }
        w.next(&mut at)?;
    }
}
