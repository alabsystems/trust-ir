// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    clippy::while_let_loop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        caller: &Function,
        inst: &Inst,
        values: &ObservedValueTypes,
        nominal: Option<&ObservedNominalTypeReachability<'_>>,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<&Inst>() + size_of::<bool>())?;
        let (callee, args, refine_deferred) = match inst {
            Inst::Call { callee, args } | Inst::CallCannotUnwind { callee, args } => {
                (*callee, args, true)
            }
            Inst::Invoke { callee, args, .. } => (*callee, args, false),
            _ => return Ok(()),
        };
        let Some(target) = catalog.unique_observed(callee, work.session, work.site)? else {
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::CalleeNotFound {
                block: block.index(),
                callee_id: callee.index(),
            });
            return Ok(());
        };
        let module = catalog.source_module();
        let Some(signature) = work.at(&module.func_types, target.ty.as_usize())? else {
            work.text(&target.name, &mut self.name)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::FuncTypeNotFound {
                func_name: take(&mut self.name),
                func_ty_id: target.ty.index(),
            });
            return Ok(());
        };
        work.admit(3, 2 * size_of::<usize>() + size_of::<bool>())?;
        let expected = signature.params.len();
        let actual = args.len();
        let mismatch = if signature.is_vararg {
            work.admit(1, size_of::<Vec<ValidationError>>())?;
            if self.pending.capacity() != 0 {
                return Err(ObservedValueError::InvalidRange);
            }
            self.pending = validate_nominal_varargs_observed(
                args,
                expected,
                values,
                nominal,
                &caller.name,
                work.session,
                work.site,
            )?;
            self.merge(work)?;
            actual < expected
        } else {
            actual != expected
        };
        work.admit(1, size_of::<bool>())?;
        if mismatch {
            self.count(caller, target, block, expected, actual, work)?;
        }
        let mut at = 0;
        loop {
            let Some(arg) = work.at(args, at)? else {
                break;
            };
            let Some(expected) = work.at(&signature.params, at)? else {
                break;
            };
            work.admit(1, size_of::<ValueId>())?;
            let arg = *arg;
            if let Some(actual) = values.get_observed(arg, work.session, work.site)?
                && !actual.structural_eq_observed(expected, work.session, work.site)?
            {
                work.admit(3, 3 * size_of::<bool>())?;
                if !refine_deferred || !(actual.is_refine() || expected.is_refine()) {
                    self.types(caller, target, block, at, expected, actual, work)?;
                }
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
}
