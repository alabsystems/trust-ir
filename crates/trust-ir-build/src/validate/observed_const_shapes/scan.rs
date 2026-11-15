// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, 'm>,
        nominal: Option<&ObservedNominalTypeReachability<'_>>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let module = symbols.module();
        let mut g = 0;
        while let Some(global) = work.at(&module.globals, g)? {
            work.admit(1, size_of::<Option<&ObservedNominalTypeReachability<'_>>>())?;
            if let Some(nominal) = nominal {
                if nominal.contains_handle_observed(&global.ty, work.session, work.site)? {
                    self.global_nominal(&global.name, true, work)?;
                } else if nominal.contains_dialect_observed(&global.ty, work.session, work.site)? {
                    self.global_nominal(&global.name, false, work)?;
                }
            }
            work.admit(1, size_of::<Option<&Constant>>())?;
            if let Some(c) = &global.initializer {
                self.global_location(&global.name, work)?;
                // PKG-U13e rule C1: a blob anywhere in an initializer is the
                // global's one refusal, before (and instead of) its walk.
                if self.holds_tensor_blob(c, work)? {
                    work.text(TENSOR_BLOB_IN_A_GLOBAL, &mut self.detail)?;
                    work.reserve(&mut self.errors)?;
                    work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
                    self.errors.push(ValidationError::InvalidTensorBlob {
                        location: take(&mut self.location),
                        reason: take(&mut self.detail),
                    });
                } else {
                    self.one(symbols, c, &global.ty, None, work)?;
                }
                work.flat(take(&mut self.location));
                work.admit(1, 0)?;
            }
            work.next(&mut g)?;
        }
        let mut f = 0;
        while let Some(function) = work.at(&module.functions, f)? {
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                self.block_location(function, block.id, work)?;
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    work.admit(8, size_of::<Option<&Constant>>())?;
                    match &node.inst {
                        Inst::Const { ty, value } => self.one(symbols, value, ty, None, work)?,
                        Inst::Switch { value, cases, .. } => {
                            self.switch(symbols, function, *value, cases, work)?
                        }
                        _ => {}
                    }
                    work.next(&mut n)?;
                }
                work.flat(take(&mut self.location));
                work.admit(1, 0)?;
                work.next(&mut b)?;
            }
            self.retire_values(work);
            work.admit(1, 0)?;
            work.next(&mut f)?;
        }
        Ok(())
    }
    /// Whether `constant` is, or holds anywhere, a `Constant::TensorBlob`:
    /// one admitted step per node, over the constant's own child iterators.
    fn holds_tensor_blob<O: ExecutionObserver>(
        &mut self,
        constant: &Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut pending = vec![constant];
        while let Some(next) = pending.pop() {
            work.admit(1, size_of::<&Constant>())?;
            if matches!(next, Constant::TensorBlob { .. }) {
                return Ok(true);
            }
            pending.extend(next.children());
        }
        Ok(false)
    }
}
