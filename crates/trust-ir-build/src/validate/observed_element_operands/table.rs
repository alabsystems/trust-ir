// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn table<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        role: &'static str,
        module: Option<&Module>,
        aggregate: &Ty,
        demanded: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, size_of::<(&str, &trust_ir::value::TyId)>())?;
        let (carrier, element) = match aggregate {
            Ty::Sequence(element) => ("sequence", element),
            Ty::Array(element, _) => ("array", element),
            _ => return Ok(()),
        };
        let Some(module) = module else { return Ok(()) };
        work.admit(1, size_of::<Option<&Ty>>())?;
        let Some(element_ty) = module.types.get(element.as_usize()) else {
            self.start(op, work)?;
            work.text(carrier, &mut self.reason)?;
            work.text(" element type ty#", &mut self.reason)?;
            work.number(u128::from(element.index()), &mut self.reason)?;
            work.text(" is not in the module type table", &mut self.reason)?;
            return self.commit(block, work);
        };
        if !element_ty.structural_eq_observed(demanded, work.session, work.site)?
            && !operands::consumption(element_ty, demanded, work)?
        {
            self.start(op, work)?;
            work.text(role, &mut self.reason)?;
            work.text(" must match ", &mut self.reason)?;
            work.text(carrier, &mut self.reason)?;
            work.text(" element type ", &mut self.reason)?;
            self.ty(element_ty, work)?;
            work.text(", got ", &mut self.reason)?;
            self.ty(demanded, work)?;
            self.commit(block, work)?;
        }
        Ok(())
    }
}
