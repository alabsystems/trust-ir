// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn reads<O: ExecutionObserver>(
    function: &Function,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let mut b = 0;
    while let Some(block) = work.at(&function.blocks, b)? {
        let mut n = 0;
        while let Some(node) = work.at(&block.body, n)? {
            work.admit(1, size_of::<bool>() + size_of::<u32>())?;
            if matches!(&node.inst, Inst::ExtractField { field, .. } if *field >= 1) {
                return Ok(true);
            }
            work.next(&mut n)?;
        }
        work.next(&mut b)?;
    }
    Ok(false)
}
impl State {
    pub(super) fn build<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.tag_reads(function, work)?;
        self.case_edges(function, work)?;
        // Original ordering: actual dominators are built AFTER all tag/case rows.
        self.tree = Some(DominatorTree::new_observed(
            function,
            work.session,
            work.site,
        )?);
        Ok(())
    }
    fn tag_reads<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = work.at(&function.blocks, b)? {
            let mut n = 0;
            while let Some(node) = work.at(&block.body, n)? {
                work.admit(1, size_of::<u32>())?;
                if let Inst::ExtractField {
                    aggregate,
                    field: 0,
                    ..
                } = &node.inst
                {
                    work.admit(1, size_of::<Option<&ValueId>>())?;
                    if let Some(result) = node.results.first() {
                        work.admit(2, size_of::<(u32, u32)>())?;
                        self.insert_tag(result.index(), aggregate.index(), work)?;
                    }
                }
                work.next(&mut n)?;
            }
            work.next(&mut b)?;
        }
        Ok(())
    }
    fn insert_tag<O: ExecutionObserver>(
        &mut self,
        key: u32,
        value: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut i = 0;
        while let Some(row) = work.at(&self.tags, i)? {
            work.admit(1, size_of::<bool>())?;
            if row.0 == key {
                work.admit(1, size_of::<u32>())?;
                self.tags[i].1 = value;
                return Ok(());
            }
            work.next(&mut i)?;
        }
        work.push(&mut self.tags, (key, value))
    }
    fn tag<O: ExecutionObserver>(&self, key: u32, work: &mut Work<'_, '_, O>) -> R<Option<u32>> {
        let mut i = 0;
        while let Some(row) = work.at(&self.tags, i)? {
            work.admit(1, size_of::<bool>() + size_of::<Option<u32>>())?;
            if row.0 == key {
                return Ok(Some(row.1));
            }
            work.next(&mut i)?;
        }
        Ok(None)
    }
    fn case_edges<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = work.at(&function.blocks, b)? {
            work.admit(1, size_of::<Option<&InstrNode>>())?;
            if let Some(node) = block.body.last() {
                work.admit(1, size_of::<u32>())?;
                if let Inst::Switch { value, cases, .. } = &node.inst {
                    work.admit(1, size_of::<u32>())?;
                    if let Some(scrutinee) = self.tag(value.index(), work)? {
                        let mut i = 0;
                        while let Some(case) = work.at(cases, i)? {
                            if let Some(selector) = selector(&case.value, work)? {
                                work.admit(1, size_of::<Edge>())?;
                                work.push(&mut self.edges, (block.id, i, scrutinee, selector))?;
                            }
                            work.next(&mut i)?;
                        }
                    }
                }
            }
            work.next(&mut b)?;
        }
        Ok(())
    }
}
pub(super) fn selector<O: ExecutionObserver>(
    value: &Constant,
    work: &mut Work<'_, '_, O>,
) -> R<Option<i128>> {
    work.admit(1, size_of::<Option<i128>>() + size_of::<i128>())?;
    Ok(match value {
        Constant::Int(v) => Some(*v),
        Constant::U128(v) => i128::try_from(*v).ok(),
        Constant::Bool(b) => Some(i128::from(*b)),
        _ => None,
    })
}
