// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn node<'m: 'a, O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, 'm>,
        item: Item<'a>,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<Children<'a>>> {
        work.admit(
            64,
            size_of::<ConstantChildren<'a>>()
                + size_of::<Option<Children<'a>>>()
                + size_of::<Option<&Ty>>(),
        )?;
        self.weak(symbols, item, work)?;
        if let (Constant::Int(n), Ty::Char) = (item.constant, item.ty)
            && !((0..=0x10FFFF).contains(n) && !(0xD800..=0xDFFF).contains(n))
        {
            work.text(
                "a Unicode scalar value (0..=0x10FFFF minus 0xD800..=0xDFFF)",
                &mut self.expected,
            )?;
            work.text("char constant ", &mut self.actual)?;
            work.signed(*n, &mut self.actual)?;
            self.mismatch_ready(work)?;
        }
        let mut children = item.constant.children();
        let mut indexed = true;
        let mut names = None;
        let types = match (item.constant, item.ty) {
            (Constant::Uninit, _) => return Ok(None),
            (Constant::FnDef(target), Ty::Func(signature)) => {
                self.function(symbols, *target, *signature, work)?;
                return Ok(None);
            }
            (Constant::Bytes { data, utf8 }, Ty::Array(id, len)) => {
                self.bytes(symbols.module(), data, *utf8, *id, *len, work)?;
                return Ok(None);
            }
            (Constant::Array(values) | Constant::Aggregate(values), Ty::Array(id, len)) => {
                if values.len() as u64 != *len {
                    self.mismatch(item, work)?;
                    return Ok(None);
                }
                let Some(ty) = work.at(&symbols.module().types, id.as_usize())? else {
                    self.missing("ty.", id.index(), work)?;
                    return Ok(None);
                };
                self.uniform_list(item.constant, values, work)?;
                ChildTypes::Repeated(ty)
            }
            (Constant::Splat { len: count, .. }, Ty::Array(id, len)) => {
                if count != len {
                    self.mismatch(item, work)?;
                    return Ok(None);
                }
                let Some(ty) = work.at(&symbols.module().types, id.as_usize())? else {
                    self.missing("ty.", id.index(), work)?;
                    return Ok(None);
                };
                if *count < 2 {
                    work.text("a splat of ", &mut self.spelling)?;
                    work.unsigned(u128::from(*count), &mut self.spelling)?;
                    work.text(
                        " element(s) is spelled as the list `array[ .. ]`",
                        &mut self.spelling,
                    )?;
                    self.uniform_error(work)?;
                }
                ChildTypes::Repeated(ty)
            }
            (Constant::Sequence(_), Ty::Sequence(id)) | (Constant::Set(_), Ty::Set(id, _)) => {
                let Some(ty) = work.at(&symbols.module().types, id.as_usize())? else {
                    self.missing("ty.", id.index(), work)?;
                    return Ok(None);
                };
                ChildTypes::Repeated(ty)
            }
            (Constant::Vector(values), Ty::Vector(elem, lanes)) => {
                if values.len() != *lanes as usize {
                    self.mismatch(item, work)?;
                    return Ok(None);
                }
                ChildTypes::Repeated(elem)
            }
            (Constant::Aggregate(values), Ty::Tuple(types)) => {
                if values.len() != types.len() {
                    self.mismatch(item, work)?;
                    return Ok(None);
                }
                ChildTypes::Positional(types)
            }
            (Constant::Aggregate(values), Ty::Struct(id)) => {
                let Some(fields) = self.structure(symbols.module(), values, *id, item, work)?
                else {
                    return Ok(None);
                };
                ChildTypes::Fields(fields)
            }
            (Constant::Aggregate(values), Ty::Record(id)) => {
                let Some(fields) = self.record(symbols.module(), values.len(), *id, item, work)?
                else {
                    return Ok(None);
                };
                ChildTypes::Fields(fields)
            }
            (Constant::Record(values), Ty::Record(id)) => {
                let Some(fields) = self.record(symbols.module(), values.len(), *id, item, work)?
                else {
                    return Ok(None);
                };
                names = Some(values.as_slice());
                ChildTypes::Fields(fields)
            }
            (Constant::Aggregate(values), Ty::Enum(id)) => {
                let Some(fields) = self.enumeration(symbols, values, *id, work)? else {
                    return Ok(None);
                };
                work.admit(1, size_of::<ConstantChildren<'a>>())?;
                children.next();
                indexed = false;
                ChildTypes::Positional(fields)
            }
            (Constant::Closure { captures, .. }, Ty::Closure(id)) => {
                let Some(row) = work.at(&symbols.module().closure_types, id.as_usize())? else {
                    self.missing("closure.", id.index(), work)?;
                    return Ok(None);
                };
                if captures.len() != row.captures.len() {
                    work.unsigned(row.captures.len() as u128, &mut self.expected)?;
                    work.text(" captures for closure.", &mut self.expected)?;
                    work.unsigned(u128::from(id.index()), &mut self.expected)?;
                    work.unsigned(captures.len() as u128, &mut self.actual)?;
                    work.text(" captures", &mut self.actual)?;
                    self.mismatch_ready(work)?;
                    return Ok(None);
                }
                indexed = false;
                ChildTypes::Positional(&row.captures)
            }
            (
                Constant::SymbolAddr { symbol, addend },
                Ty::Ref(pointee) | Ty::PtrConst(pointee) | Ty::PtrMut(pointee),
            ) => {
                self.thin(symbols, symbol, *addend, item.ty, pointee, work)?;
                return Ok(None);
            }
            (
                Constant::Aggregate(values),
                Ty::FatPtr(kind @ (FatPtrKind::Str | FatPtrKind::Slice(_))),
            ) if matches!(values.as_slice(), [Constant::SymbolAddr { .. }, _]) => {
                let [Constant::SymbolAddr { symbol, addend }, length] = values.as_slice() else {
                    return Err(ObservedValueError::InvalidRange);
                };
                self.fat(symbols, symbol, *addend, length, kind, item.ty, work)?;
                return Ok(None);
            }
            // PKG-U13e (§27), the original's rules C1-C4 through its one
            // refusal function; placement reads the walk's root, never the
            // path (an enum payload and a closure capture add no element).
            (Constant::TensorBlob { digest, dims }, Ty::Tensor(elem, rank)) => {
                self.tensor_blob(symbols, item.constant, digest, dims, elem, *rank, work)?;
                return Ok(None);
            }
            _ => {
                work.admit(8, size_of::<u32>())?;
                if !item.constant.value_matches_ty_observed(
                    item.ty,
                    symbols.module().pointer_bits(),
                    work.session,
                    work.site,
                )? {
                    self.mismatch(item, work)?
                }
                return Ok(None);
            }
        };
        Ok(Some(Children {
            constants: children,
            types,
            names,
            index: 0,
            indexed,
        }))
    }
}
