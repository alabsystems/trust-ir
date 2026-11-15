// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn thin<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, '_>,
        symbol: &str,
        addend: i64,
        ty: &Ty,
        pointee: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.thin_reason(symbols, symbol, addend, ty, pointee, work)?;
        work.admit(1, size_of::<bool>())?;
        if self.reason.is_some() {
            self.pointer_error(symbol, ty, work)?;
        }
        Ok(())
    }
    fn thin_reason<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, '_>,
        symbol: &str,
        addend: i64,
        ty: &Ty,
        pointee: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            64,
            size_of::<PointerConstantRefusal>() + size_of::<Option<&trust_ir::Global>>(),
        )?;
        let global = match symbols.target_global_observed(symbol, work.session, work.site)? {
            Ok(g) => g,
            Err(reason) => {
                self.reason = Some(reason);
                return Ok(());
            }
        };
        if addend != 0 {
            self.reason = Some(PointerConstantRefusal::NonzeroAddend { addend });
            return Ok(());
        }
        if !type_equal(symbols.module(), &global.ty, pointee, work)? {
            self.render = global.ty.display_observed(work.session, work.site)?;
            work.admit(1, size_of::<PointerConstantRefusal>() + size_of::<String>())?;
            self.reason = Some(PointerConstantRefusal::PointeeTypeMismatch {
                global_ty: take(&mut self.render),
            });
            return Ok(());
        }
        work.admit(8, size_of::<bool>())?;
        let valid = match ty {
            Ty::Ref(_) => !global.mutable,
            Ty::PtrMut(_) => global.mutable,
            _ => true,
        };
        if !valid {
            self.reason = Some(PointerConstantRefusal::MutabilityMismatch {
                global_mutable: global.mutable,
            });
        }
        Ok(())
    }
    pub(super) fn fat<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, '_>,
        symbol: &str,
        addend: i64,
        length: &Constant,
        kind: &FatPtrKind,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.fat_reason(symbols, symbol, addend, length, kind, work)?;
        work.admit(1, size_of::<bool>())?;
        if self.reason.is_some() {
            self.pointer_error(symbol, ty, work)?;
        }
        Ok(())
    }
    fn fat_reason<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, '_>,
        symbol: &str,
        addend: i64,
        length: &Constant,
        kind: &FatPtrKind,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            96,
            size_of::<PointerConstantRefusal>()
                + 4 * size_of::<u128>()
                + 4 * size_of::<u64>()
                + size_of::<Option<&trust_ir::Global>>(),
        )?;
        let global = match symbols.target_global_observed(symbol, work.session, work.site)? {
            Ok(g) => g,
            Err(reason) => {
                self.reason = Some(reason);
                return Ok(());
            }
        };
        if global.mutable {
            self.reason = Some(PointerConstantRefusal::MutabilityMismatch {
                global_mutable: true,
            });
            return Ok(());
        }
        let Constant::Int(n) = length else {
            self.render = length.shape_label_observed(work.session, work.site)?;
            return self.invalid_length(work);
        };
        let Ok(length) = u64::try_from(*n) else {
            work.signed(*n, &mut self.render)?;
            return self.invalid_length(work);
        };
        let Ty::Array(element, capacity) = &global.ty else {
            return self.not_array(&global.ty, work);
        };
        let capacity = *capacity;
        let Ok(offset) = u64::try_from(addend) else {
            return self.bounds(addend, length, capacity, work);
        };
        let Some(element_ty) = work.at(&symbols.module().types, element.as_usize())? else {
            return self.not_array(&global.ty, work);
        };
        match kind {
            FatPtrKind::Str => {
                work.admit(32, 2 * size_of::<u128>() + size_of::<Option<&[u8]>>())?;
                if !matches!(element_ty, Ty::U8) {
                    return self.not_array(&global.ty, work);
                }
                if u128::from(offset) + u128::from(length) > u128::from(capacity) {
                    return self.bounds(addend, length, capacity, work);
                }
                let Some(Constant::Bytes { data, utf8: true }) = &global.initializer else {
                    self.reason = Some(PointerConstantRefusal::NotUtf8Bytes);
                    return Ok(());
                };
                // The preceding u128 capacity comparison implies this exact
                // sum fits u64; malformed initializer lengths still use get.
                let end = offset
                    .checked_add(length)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let window = usize::try_from(offset)
                    .ok()
                    .zip(usize::try_from(end).ok())
                    .and_then(|(start, end)| data.get(start..end));
                let Some(window) = window else {
                    return self.bounds(addend, length, capacity, work);
                };
                // Only the original selected window is checked here. A false
                // full-global UTF8 claim is the full initializer walk's rule.
                if !utf8_is_valid_observed(window, work.session, work.site)? {
                    self.reason = Some(PointerConstantRefusal::NotOnCharBoundary);
                }
                Ok(())
            }
            FatPtrKind::Slice(slice_element) => {
                let Some(slice_ty) = work.at(&symbols.module().types, slice_element.as_usize())?
                else {
                    return self.not_array(&global.ty, work);
                };
                if !type_equal(symbols.module(), element_ty, slice_ty, work)? {
                    return self.not_array(&global.ty, work);
                }
                // Whole child Arc/error is State-held BEFORE any next fee;
                // outer operational refusal never becomes semantic unknown.
                match symbols
                    .layouts()
                    .ty_layout_observed(element_ty, work.session, work.site)?
                {
                    Ok(shape) => self.layout = Some(shape),
                    Err(error) => self.layout_error = Some(error),
                }
                work.admit(32, 4 * size_of::<u64>() + 2 * size_of::<u128>())?;
                if self.layout_error.is_some() {
                    self.reason = Some(PointerConstantRefusal::ElementLayoutUnknown);
                    return Ok(());
                }
                let size = self
                    .layout
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .size_bits
                    / 8;
                let start = match size {
                    0 if offset == 0 => 0,
                    0 => return self.bounds(addend, length, capacity, work),
                    size if offset % size == 0 => offset / size,
                    size => {
                        self.reason = Some(PointerConstantRefusal::MisalignedOffset {
                            offset: addend,
                            element_size: size,
                        });
                        return Ok(());
                    }
                };
                if u128::from(start) + u128::from(length) > u128::from(capacity) {
                    return self.bounds(addend, length, capacity, work);
                }
                Ok(())
            }
            _ => Err(ObservedValueError::InvalidRange),
        }
    }
    fn invalid_length<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<PointerConstantRefusal>() + size_of::<String>())?;
        self.reason = Some(PointerConstantRefusal::InvalidLength {
            length: take(&mut self.render),
        });
        Ok(())
    }
    fn not_array<O: ExecutionObserver>(&mut self, ty: &Ty, work: &mut Work<'_, '_, O>) -> R {
        self.render = ty.display_observed(work.session, work.site)?;
        work.admit(1, size_of::<PointerConstantRefusal>() + size_of::<String>())?;
        self.reason = Some(PointerConstantRefusal::ArrayTypeMismatch {
            global_ty: take(&mut self.render),
        });
        Ok(())
    }
    fn bounds<O: ExecutionObserver>(
        &mut self,
        offset: i64,
        length: u64,
        capacity: u64,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<PointerConstantRefusal>())?;
        self.reason = Some(PointerConstantRefusal::WindowOutOfBounds {
            offset,
            length,
            capacity,
        });
        Ok(())
    }
}
/// Exact full module-aware relation, including active-path/coinductive and
/// predicate/nominal/ABI rules. The actual child consumes any diagnostic
/// conflict before this bool returns; no callback or raw type-ID shortcut.
fn type_equal<O: ExecutionObserver>(
    module: &Module,
    a: &Ty,
    b: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    trust_ir::imports::ty_structurally_eq_across_observed(
        module,
        a,
        module,
        b,
        work.session,
        work.site,
    )
}
