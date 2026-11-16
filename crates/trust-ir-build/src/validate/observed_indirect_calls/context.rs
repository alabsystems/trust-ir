// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'c, 'm> ObservedIndirectCalls<'c, 'm> {
    /// The full caller constructs one context for the actual physical function
    /// when its original complete census selects indirect work. The original
    /// local closure map is eager; the pointer component borrows only initially.
    pub(in crate::validate) fn new_observed<O: ExecutionObserver>(
        catalog: &'c ModuleFunctionCatalog<'m>,
        physical_function: usize,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Self>() + size_of::<Work<'_, '_, O>>())?;
        let function = work
            .at(&catalog.source_module().functions, physical_function)?
            .ok_or(ObservedValueError::InvalidRange)?;
        let mut out = Self {
            catalog,
            function,
            closures: None,
            pointers: None,
            item_origins: None,
        };
        let result: R = (|| {
            work.admit(1, size_of::<Option<ObservedLocalClosureTargets<'_>>>())?;
            out.closures = Some(ObservedLocalClosureTargets::new_observed(
                function,
                work.session,
                work.site,
            )?);
            work.admit(
                1,
                size_of::<Option<ObservedStaticFunctionPointerAnalysis<'_>>>(),
            )?;
            out.pointers = Some(ObservedStaticFunctionPointerAnalysis::new_observed(
                function,
                work.session,
                work.site,
            )?);
            work.publication(size_of::<Self>())
        })();
        if let Err(error) = result {
            out.retire_inner(&mut work);
            return Err(work.terminal(error));
        }
        Ok(out)
    }
    pub(super) fn has_item_origins<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        if let Some(answer) = self.item_origins {
            return Ok(answer);
        }
        let mut b = 0;
        while let Some(block) = work.at(&self.function.blocks, b)? {
            let mut n = 0;
            while let Some(node) = work.at(&block.body, n)? {
                work.admit(4, size_of::<bool>())?;
                if matches!(&node.inst, Inst::Const { ty: Ty::FnItem(expected),
                    value: Constant::FnItem(actual) } if expected == actual)
                {
                    self.item_origins = Some(true);
                    return Ok(true);
                }
                work.next(&mut n)?;
            }
            work.next(&mut b)?;
        }
        self.item_origins = Some(false);
        Ok(false)
    }
    /// Consume all derived private caches under the same original caller owner.
    pub(in crate::validate) fn retire_observed<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        self.retire_inner(&mut work);
        work.publication(0)
    }
    pub(super) fn retire_inner<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Self>() + 1);
        if let Some(closures) = self.closures.take() {
            let _ = closures.retire_observed(work.session, work.site);
        }
        work.poll();
        if let Some(pointers) = self.pointers.take() {
            let _ = pointers.retire_observed(work.session, work.site);
        }
        work.poll();
    }
}
