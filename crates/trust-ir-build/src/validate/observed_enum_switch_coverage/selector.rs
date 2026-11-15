// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn width<O: ExecutionObserver>(
    ty: &Ty,
    pointer_bits: u32,
    w: &mut Work<'_, '_, O>,
) -> R<Option<u32>> {
    w.admit(32, size_of::<Option<u32>>())?;
    Ok(if ty.is_integer() || matches!(ty, Ty::Char) {
        ty.bit_width_with(pointer_bits)
    } else {
        None
    })
}
fn definition<'m, O: ExecutionObserver>(
    module: &'m Module,
    id: EnumId,
    w: &mut Work<'_, '_, O>,
) -> R<Option<&'m EnumDef>> {
    if let Some(d) = w.at(&module.enums, id.as_usize())? {
        w.admit(2, size_of::<bool>())?;
        if d.id == id {
            return Ok(Some(d));
        }
    }
    let mut at = 0;
    while let Some(d) = w.at(&module.enums, at)? {
        w.admit(2, size_of::<bool>())?;
        if d.id == id {
            return Ok(Some(d));
        }
        w.next(&mut at)?;
    }
    Ok(None)
}
pub(super) fn tag_bits<O: ExecutionObserver>(
    def: &EnumDef,
    w: &mut Work<'_, '_, O>,
) -> R<Option<u32>> {
    let Some(repr) = def.canonical_tag_repr_observed(w.session, w.site)? else {
        return Ok(None);
    };
    w.admit(32, size_of::<Ty>() + size_of::<Option<u32>>())?;
    Ok(repr.ty().bit_width())
}
impl<'f, 'm> State<'f, 'm> {
    pub(super) fn selector<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        values: &ObservedValueTypes,
        selector: ValueId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(
            8,
            3 * size_of::<u32>() + size_of::<ValueId>() + size_of::<usize>(),
        )?;
        let pointer_bits = module.pointer_bits();
        let Some(ty) = values.get_observed(selector, w.session, w.site)? else {
            return Ok(false);
        };
        let Some(selector_width) = width(ty, pointer_bits, w)? else {
            return Ok(false);
        };
        let mut expect = selector_width;
        let mut current = selector;
        let count = self
            .definitions
            .len()
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let mut at = 0;
        while at < count {
            let Some(inst) = self.unique(current, w)? else {
                return Ok(false);
            };
            w.admit(64, size_of::<Option<Widen>>())?;
            match inst {
                Inst::Copy { operand, .. } => current = *operand,
                Inst::Cast {
                    op,
                    src_ty,
                    dst_ty,
                    operand,
                } => {
                    let Some(from) = width(src_ty, pointer_bits, w)? else {
                        return Ok(false);
                    };
                    let Some(to) = width(dst_ty, pointer_bits, w)? else {
                        return Ok(false);
                    };
                    if to != expect {
                        return Ok(false);
                    }
                    let step = match op {
                        CastOp::ZExt if to >= from => Widen::Zero { to },
                        CastOp::SExt if to >= from => Widen::Sign { from, to },
                        CastOp::Bitcast if to == from => Widen::Zero { to },
                        _ => return Ok(false),
                    };
                    w.reserve(&mut self.widen)?;
                    w.admit(1, size_of::<Widen>())?;
                    self.widen.push(step);
                    expect = from;
                    current = *operand;
                }
                Inst::ExtractField {
                    aggregate,
                    field: 0,
                    ..
                } => {
                    let Some(ty) = values.get_observed(*aggregate, w.session, w.site)? else {
                        return Ok(false);
                    };
                    w.admit(32, size_of::<Option<EnumId>>())?;
                    let Ty::Enum(id) = ty else { return Ok(false) };
                    let Some(def) = definition(module, *id, w)? else {
                        return Ok(false);
                    };
                    let Some(tag_bits) = tag_bits(def, w)? else {
                        return Ok(false);
                    };
                    if tag_bits != expect {
                        return Ok(false);
                    }
                    w.admit(1, size_of::<Option<Selection<'m>>>())?;
                    self.selection = Some(Selection {
                        definition: def,
                        width: selector_width,
                    });
                    self.enum_ty = ty.display_observed(w.session, w.site)?;
                    return Ok(true);
                }
                _ => return Ok(false),
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
