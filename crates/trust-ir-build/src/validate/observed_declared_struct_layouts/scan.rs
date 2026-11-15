// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn scoped(error: &ValidationError) -> Option<u32> {
    match error {
        ValidationError::StructLayoutInconsistent { struct_id, .. }
        | ValidationError::TargetScalarLayoutUnavailable { struct_id, .. }
        | ValidationError::PackedReprInvalidAlign { struct_id, .. }
        | ValidationError::TransparentReprFieldCount { struct_id, .. } => Some(*struct_id),
        _ => None,
    }
}
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        prior: &[ValidationError],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.table.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.table = Some(LayoutTable::new_observed(module, work.session, work.site)?);
        self.precise(module, work)?;
        // Freeze the original suppression set before generic errors are added.
        // Later generic errors must not suppress another physical same-ID row.
        self.prior(prior, work)?;
        let mut e = 0;
        while let Some(error) = work.at(&self.errors, e)? {
            work.admit(1, size_of::<Option<u32>>())?;
            if let Some(id) = scoped(error) {
                work.reserve(&mut self.reported)?;
                work.admit(1, size_of::<u32>())?;
                self.reported.push(id);
            }
            work.next(&mut e)?;
        }
        let mut n = 0;
        while let Some(row) = work.at(&module.structs, n)? {
            work.admit(3, 2 * size_of::<Option<u64>>())?;
            let id = row.id.index();
            if row.size.is_none() || row.align.is_none() {
                work.next(&mut n)?;
                continue;
            }
            let mut at = 0;
            let mut known = false;
            while let Some(prior) = work.at(&self.reported, at)? {
                work.admit(1, 0)?;
                if *prior == id {
                    known = true;
                    break;
                }
                work.next(&mut at)?;
            }
            if known {
                work.next(&mut n)?;
                continue;
            }
            if self.query(&Ty::Struct(row.id), work)?.is_none() {
                work.admit(1, 0)?;
                let incoherent = matches!(&self.error,Some(LayoutError::StructLayoutIncoherent(other)) if *other==row.id);
                if incoherent {
                    self.retire_error(work);
                    work.admit(1, 0)?;
                    self.push(id, STRUCT_LAYOUT_INCOHERENT_REASON, work)?;
                } else if self.take_target(work)? {
                    self.target_error(id, work)?;
                }
            }
            work.next(&mut n)?;
        }
        Ok(())
    }
    fn prior<O: ExecutionObserver>(
        &mut self,
        prior: &[ValidationError],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(error) = work.at(prior, index)? {
            work.admit(1, size_of::<Option<u32>>())?;
            if let Some(id) = scoped(error) {
                work.reserve(&mut self.reported)?;
                work.admit(1, size_of::<u32>())?;
                self.reported.push(id);
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
}
