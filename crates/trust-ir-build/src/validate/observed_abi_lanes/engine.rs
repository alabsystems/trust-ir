// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        memo: &mut ObservedAbiLanes<'_>,
        layouts: &LayoutTable<'a>,
        root: &'a Ty,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        let mut action = Action::Enter(root);
        loop {
            w.admit(2, size_of::<Action<'_>>())?;
            action = match action {
                Action::Enter(ty) => self.enter(memo, layouts, ty, w)?,
                Action::Return(count) => {
                    if self.frames.is_empty() {
                        return Ok(count);
                    }
                    self.resume(memo, count, w)?
                }
                Action::Sum(fields, owner) => self.sum(fields, owner, w)?,
                Action::NextVariant => self.next_variant(memo, w)?,
                Action::Summed(owner, count) => self.summed(memo, owner, count, w)?,
            };
        }
    }

    fn size<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'a>,
        ty: &Ty,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<u64>> {
        w.admit(
            1,
            size_of::<Option<Result<Arc<TyLayoutShape>, LayoutError>>>(),
        )?;
        if self.layout.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.layout = Some(layouts.ty_layout_observed(ty, w.session, w.site)?);
        w.admit(6, size_of::<Option<u64>>())?;
        let answer = match &self.layout {
            Some(Ok(shape)) => shape.size_bytes(),
            _ => None,
        };
        self.retire_layout(w)?;
        w.admit(1, 0)?;
        Ok(answer)
    }
    fn enter<O: ExecutionObserver>(
        &mut self,
        memo: &mut ObservedAbiLanes<'_>,
        layouts: &LayoutTable<'a>,
        ty: &'a Ty,
        w: &mut Work<'_, '_, O>,
    ) -> R<Action<'a>> {
        w.admit(67, size_of::<&Ty>())?;
        if is_closed_scalar_ty(ty) {
            return Ok(Action::Return(
                self.size(layouts, ty, w)?
                    .map(|size| usize::from(size != 0)),
            ));
        }
        match ty {
            Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_) => {
                Ok(Action::Return(Some(1)))
            }
            Ty::FatPtr(_) => Ok(Action::Return(Some(2))),
            Ty::Tuple(fields) => Ok(Action::Sum(Fields::Types(fields), Owner::Inline)),
            Ty::Struct(id) => {
                let node = Node::Struct(*id);
                if let Some(slot) = memo.read(node, w)? {
                    return Ok(Action::Return(match slot {
                        Slot::Open => None,
                        Slot::Counted(count) => count,
                    }));
                }
                let mut i = 0;
                let mut found = None;
                while let Some(def) = w.at(&layouts.module().structs, i)? {
                    w.admit(1, size_of::<bool>())?;
                    if def.id == *id {
                        found = Some(def);
                        break;
                    }
                    w.next(&mut i)?;
                }
                let Some(def) = found else {
                    memo.write(node, Slot::Counted(None), w)?;
                    return Ok(Action::Return(None));
                };
                memo.write(node, Slot::Open, w)?;
                Ok(Action::Sum(Fields::Struct(&def.fields), Owner::Struct(*id)))
            }
            Ty::Enum(id) => {
                let node = Node::Enum(*id);
                if let Some(slot) = memo.read(node, w)? {
                    return Ok(Action::Return(match slot {
                        Slot::Open => None,
                        Slot::Counted(count) => count,
                    }));
                }
                let mut i = 0;
                let mut found = None;
                while let Some(def) = w.at(&layouts.module().enums, i)? {
                    w.admit(1, size_of::<bool>())?;
                    if def.id == *id {
                        found = Some(def);
                        break;
                    }
                    w.next(&mut i)?;
                }
                let Some(def) = found else {
                    memo.write(node, Slot::Counted(None), w)?;
                    return Ok(Action::Return(None));
                };
                w.admit(1, size_of::<bool>())?;
                if def.variants.is_empty() {
                    memo.write(node, Slot::Counted(None), w)?;
                    return Ok(Action::Return(None));
                }
                w.admit(16, size_of::<Rule>())?;
                let rule = match def.layout.as_ref().map(|layout| &layout.encoding) {
                    Some(EnumTagEncoding::Untagged) => {
                        if def.variants.len() != 1 {
                            memo.write(node, Slot::Counted(None), w)?;
                            return Ok(Action::Return(None));
                        }
                        Rule::Untagged { variant: 0 }
                    }
                    Some(EnumTagEncoding::SingleInhabited { variant }) => {
                        let active = *variant as usize;
                        let mut valid = active < def.variants.len();
                        for (index, item) in def.variants.iter().enumerate() {
                            w.admit(1, size_of::<bool>())?;
                            let uninhabited =
                                layouts.variant_is_uninhabited_observed(item, w.session, w.site)?;
                            if uninhabited == (index == active) {
                                valid = false;
                            }
                        }
                        if !valid {
                            memo.write(node, Slot::Counted(None), w)?;
                            return Ok(Action::Return(None));
                        }
                        Rule::Untagged { variant: active }
                    }
                    Some(EnumTagEncoding::Niche {
                        untagged_variant, ..
                    }) => Rule::Niche {
                        dataful: *untagged_variant as usize,
                    },
                    Some(EnumTagEncoding::Direct { .. }) | None => Rule::Direct { widest: 0 },
                };
                memo.write(node, Slot::Open, w)?;
                w.push(
                    &mut self.frames,
                    Frame::Enum {
                        id: *id,
                        def,
                        rule,
                        counted: 0,
                    },
                )?;
                Ok(Action::NextVariant)
            }
            _ => Ok(Action::Return(None)),
        }
    }
}
