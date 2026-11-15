// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'m> State<'m> {
    pub(super) fn slots<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'m>,
        function: &'m Function,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(signature) = w.at(&layouts.module().func_types, function.ty.as_usize())? else {
            return Ok(());
        };
        let mut i = 0;
        while let Some(ty) = w.at(&signature.params, i)? {
            if let Some(attrs) = w.at(&function.attrs.params, i)? {
                w.text("parameter ", &mut self.slot)?;
                w.unsigned(i as u128, &mut self.slot)?;
                self.check(layouts, function, ty, attrs, w)?;
                w.admit(16, 0)?;
                let indirect = matches!(attrs.pass, Some(PassMode::Indirect { .. }));
                if (attrs.byval || attrs.sret) && attrs.pass.is_some() && !indirect {
                    w.text("`", &mut self.detail)?;
                    w.text(if attrs.byval { "byval" } else { "sret" }, &mut self.detail)?;
                    w.text(
                        "` says the aggregate crosses through memory, but the pass mode says `",
                        &mut self.detail,
                    )?;
                    w.text(
                        attrs.pass.as_ref().map_or("none", PassMode::token),
                        &mut self.detail,
                    )?;
                    w.text("`", &mut self.detail)?;
                    self.commit(function, w)?;
                }
                w.flat(take(&mut self.slot));
                w.admit(1, 0)?;
            }
            w.next(&mut i)?;
        }
        i = signature.params.len();
        while let Some(attrs) = w.at(&function.attrs.params, i)? {
            w.admit(32, 0)?;
            if !attrs.is_empty() {
                w.text("parameter ", &mut self.slot)?;
                w.unsigned(i as u128, &mut self.slot)?;
                w.text("the signature has ", &mut self.detail)?;
                w.unsigned(signature.params.len() as u128, &mut self.detail)?;
                w.text(" parameters, so this slot does not exist", &mut self.detail)?;
                self.commit(function, w)?;
                w.flat(take(&mut self.slot));
                w.admit(1, 0)?;
            }
            w.next(&mut i)?;
        }
        w.admit(32, 0)?;
        if !function.attrs.ret.is_empty() {
            let ret = &function.attrs.ret;
            w.text("return slot", &mut self.slot)?;
            for (set, name) in [
                (ret.byval, "byval"),
                (ret.sret, "sret"),
                (ret.readonly, "readonly"),
            ] {
                w.admit(1, 0)?;
                if set {
                    w.text("`", &mut self.detail)?;
                    w.text(name, &mut self.detail)?;
                    w.text(
                        "` is a parameter attribute, not a return-slot fact",
                        &mut self.detail,
                    )?;
                    self.commit(function, w)?;
                }
            }
            w.admit(2, size_of::<Option<&Ty>>())?;
            if let [ty] = signature.returns.as_slice() {
                self.check(layouts, function, ty, ret, w)?;
                w.admit(2, 0)?;
                if matches!(ret.pass, Some(PassMode::Indirect { on_stack: true })) {
                    w.text("`indirect(true)` (on_stack) describes an argument's home; a returned value has none",&mut self.detail)?;
                    self.commit(function, w)?;
                }
            } else {
                w.text("return-slot ABI facts need exactly one returned value; this signature returns ",&mut self.detail)?;
                w.unsigned(signature.returns.len() as u128, &mut self.detail)?;
                self.commit(function, w)?;
            }
            w.flat(take(&mut self.slot));
            w.admit(1, 0)?;
        }
        Ok(())
    }
    fn check<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'m>,
        function: &Function,
        ty: &'m Ty,
        attrs: &ParamAttrs,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(67, 0)?;
        if attrs.ext != ArgExt::None {
            let extendable = matches!(
                ty,
                Ty::I8 | Ty::I16 | Ty::I32 | Ty::U8 | Ty::U16 | Ty::U32 | Ty::Bool | Ty::Char
            );
            if !extendable {
                w.text("`", &mut self.detail)?;
                w.text(attrs.ext.token().unwrap_or("none"), &mut self.detail)?;
                w.text("` is admitted only on an integer / Bool / Char slot narrower than 64 bits, not on ",&mut self.detail)?;
                self.text_ty(ty, w)?;
                self.commit(function, w)?;
            }
        }
        match &attrs.pass {
            None | Some(PassMode::Direct) => {}
            Some(PassMode::Ignore) => {
                let size = self.size(layouts, ty, w)?;
                if size != Some(0) {
                    w.text("`ignore` ", &mut self.detail)?;
                    match size {
                        Some(size) => {
                            w.text("is admitted only on a zero-sized slot; ", &mut self.detail)?;
                            self.text_ty(ty, w)?;
                            w.text(" is ", &mut self.detail)?;
                            w.unsigned(u128::from(size), &mut self.detail)?;
                            w.text(" bytes", &mut self.detail)?;
                        }
                        None => {
                            w.text("needs a computable layout, and ", &mut self.detail)?;
                            self.text_ty(ty, w)?;
                            w.text(" has none", &mut self.detail)?;
                        }
                    }
                    self.commit(function, w)?;
                }
            }
            Some(PassMode::Pair) => {
                w.admit(1, 0)?;
                let count = self
                    .lanes
                    .as_mut()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .lanes_observed(layouts, ty, w.session, w.site)?;
                if count != Some(2) {
                    w.text("`pair` is admitted only on a two-scalar-lane aggregate or a fat pointer, not on ",&mut self.detail)?;
                    self.text_ty(ty, w)?;
                    self.commit(function, w)?;
                }
            }
            Some(PassMode::Cast { pieces }) => self.cast(layouts, function, ty, pieces, w)?,
            Some(PassMode::Indirect { .. }) => {
                let aggregate = layouts
                    .module()
                    .is_by_value_aggregate_slot_observed(ty, w.session, w.site)?;
                w.admit(4, 0)?;
                if !aggregate && !(attrs.byval || attrs.sret) {
                    w.text("`indirect` is admitted only on an aggregate slot, or on the `byval`/`sret` pointer that stands for one, not on ",&mut self.detail)?;
                    self.text_ty(ty, w)?;
                    self.commit(function, w)?;
                }
            }
        }
        Ok(())
    }
}
