// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'m> State<'m> {
    pub(super) fn switch<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, 'm>,
        function: &Function,
        value: ValueId,
        cases: &'m [trust_ir::inst::SwitchCase],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<ObservedValueTypes>>())?;
        if self.values.is_none() {
            self.values = Some(build_catalog_value_types_observed(
                function,
                symbols.functions(),
                work.session,
                work.site,
            )?);
        }
        let Some(selector) = self.selector(symbols.module(), value, work)? else {
            return Ok(());
        };
        let mut at = 0;
        while let Some(case) = work.at(cases, at)? {
            self.one(symbols, &case.value, &selector, Some(at), work)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn selector<O: ExecutionObserver>(
        &self,
        module: &Module,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<Ty>> {
        work.admit(32, size_of::<Option<Ty>>() + 2 * size_of::<Option<&Ty>>())?;
        let values = self
            .values
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let Some(ty) = values.get_observed(value, work.session, work.site)? else {
            return Ok(None);
        };
        // Original representation_ty unwraps ONE Refine row only. A dangling
        // or nested Refine, absent/noninteger selector stays this local skip;
        // its independent SSA/type/selector defects remain mandatory.
        let ty = if let Ty::Refine(base, _) = ty {
            let Some(base) = work.at(&module.types, base.as_usize())? else {
                return Ok(None);
            };
            base
        } else {
            ty
        };
        // Only actual scalar enum carriers are copied here: no hidden clone
        // or borrowed map payload survives a mutable parent call.
        Ok(Some(match ty {
            Ty::I8 => Ty::I8,
            Ty::I16 => Ty::I16,
            Ty::I32 => Ty::I32,
            Ty::I64 => Ty::I64,
            Ty::I128 => Ty::I128,
            Ty::Isize => Ty::Isize,
            Ty::U8 => Ty::U8,
            Ty::U16 => Ty::U16,
            Ty::U32 => Ty::U32,
            Ty::U64 => Ty::U64,
            Ty::U128 => Ty::U128,
            Ty::Usize => Ty::Usize,
            Ty::Char => Ty::Char,
            _ => return Ok(None),
        }))
    }
}
