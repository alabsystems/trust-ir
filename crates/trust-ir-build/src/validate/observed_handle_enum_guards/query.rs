// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn selected<O: ExecutionObserver>(
    guards: &ObservedHandleEnumGuards<'_>,
    block: BlockId,
    aggregate: u32,
    discriminants: &[i128],
    output: &mut Vec<usize>,
    work: &mut Work<'_, '_, O>,
) -> R {
    let mut edge = 0;
    while let Some(row) = work.at(&guards.edges, edge)? {
        work.admit(1, size_of::<Edge>() + size_of::<bool>())?;
        let (source, index, scrutinee, selector) = *row;
        if scrutinee == aggregate
            && guards.dominators.edge_dominates_observed(
                source,
                index,
                block,
                work.session,
                work.site,
            )?
        {
            let mut first = None;
            let mut unique = true;
            let mut i = 0;
            while let Some(disc) = work.at(discriminants, i)? {
                work.admit(1, size_of::<i128>() + size_of::<bool>())?;
                if *disc == selector {
                    work.admit(1, size_of::<Option<usize>>() + size_of::<bool>())?;
                    if first.is_some() {
                        unique = false;
                        break; // Same original second-match short circuit; tail stays unread.
                    }
                    first = Some(i);
                }
                work.next(&mut i)?;
            }
            if unique && let Some(variant) = first {
                work.push(output, variant)?;
            }
        }
        work.next(&mut edge)?;
    }
    Ok(())
}
