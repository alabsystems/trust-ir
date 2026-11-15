// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn weak<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, '_>,
        item: Item<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(16, size_of::<Option<&Function>>())?;
        match item.constant {
            Constant::FnDef(id) | Constant::Closure { func: id, .. } => {
                if let Some(f) =
                    symbols
                        .functions()
                        .unique_observed(*id, work.session, work.site)?
                {
                    work.admit(8, size_of::<bool>())?;
                    if f.is_weak_declaration() {
                        self.here(work)?;
                        work.text(&f.name, &mut self.symbol)?;
                        work.reserve(&mut self.errors)?;
                        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
                        self.errors.push(ValidationError::WeakDeclarationAsFnDef {
                            location: take(&mut self.location),
                            function: id.index(),
                            name: take(&mut self.symbol),
                        });
                    }
                }
            }
            Constant::SymbolAddr { symbol, addend }
                if symbols.weak_symbol_observed(symbol, work.session, work.site)? =>
            {
                work.admit(8, size_of::<i64>())?;
                match (item.ty, *addend) {
                    (Ty::Ptr, 0) => return Ok(()),
                    (Ty::Ptr, n) => {
                        work.text("ptr with nonzero addend ", &mut self.actual)?;
                        work.signed(i128::from(n), &mut self.actual)?;
                    }
                    (ty, n) => {
                        work.text("type ", &mut self.actual)?;
                        self.render_actual_ty(ty, work)?;
                        if n != 0 {
                            work.text(" with nonzero addend ", &mut self.actual)?;
                            work.signed(i128::from(n), &mut self.actual)?;
                        }
                    }
                }
                self.here(work)?;
                work.text(symbol, &mut self.symbol)?;
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
                self.errors
                    .push(ValidationError::WeakDeclarationAddressNotNullable {
                        location: take(&mut self.location),
                        symbol: take(&mut self.symbol),
                        detail: take(&mut self.actual),
                    });
            }
            _ => {}
        }
        Ok(())
    }
}
