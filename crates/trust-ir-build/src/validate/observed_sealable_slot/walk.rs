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
        module: &'a Module,
        nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.push(&mut self.frames, Frame::Type(ty))?;
        loop {
            work.admit(1, size_of::<Option<Frame<'a>>>())?;
            let Some(frame) = self.frames.pop() else {
                return Ok(true);
            };
            work.admit(1, size_of::<Frame<'a>>())?;
            match frame {
                Frame::Type(ty) => match ty {
                    Ty::Handle(_) => {}
                    Ty::Struct(id) => {
                        let mut at = 0;
                        while let Some(active) = work.at(&self.visiting, at)? {
                            work.admit(1, size_of::<bool>())?;
                            if active == id {
                                return Ok(false);
                            }
                            work.next(&mut at)?;
                        }
                        let Some(def) = structure(module, *id, work)? else {
                            return Ok(false);
                        };
                        work.push(&mut self.visiting, *id)?;
                        work.push(&mut self.frames, Frame::Fields(&def.fields, 0, *id))?;
                    }
                    Ty::Tuple(lanes) => work.push(&mut self.frames, Frame::Tuple(lanes, 0))?,
                    _ => return Ok(false),
                },
                Frame::Fields(fields, index, owner) => {
                    if let Some(field) = work.at(fields, index)? {
                        let mut next = index;
                        work.next(&mut next)?;
                        work.push(&mut self.frames, Frame::Fields(fields, next, owner))?;
                        if nominal.contains_handle_observed(&field.ty, work.session, work.site)? {
                            work.push(&mut self.frames, Frame::Type(&field.ty))?;
                        }
                    } else {
                        work.admit(1, size_of::<Option<StructId>>())?;
                        if self.visiting.pop() != Some(owner) {
                            return Err(ObservedValueError::InvalidRange);
                        }
                    }
                }
                Frame::Tuple(lanes, index) => {
                    if let Some(lane) = work.at(lanes, index)? {
                        let mut next = index;
                        work.next(&mut next)?;
                        work.push(&mut self.frames, Frame::Tuple(lanes, next))?;
                        if nominal.contains_handle_observed(lane, work.session, work.site)? {
                            work.push(&mut self.frames, Frame::Type(lane))?;
                        }
                    }
                }
            }
        }
    }
}
fn structure<'a, O: ExecutionObserver>(
    module: &'a Module,
    id: StructId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a StructDef>> {
    work.admit(1, size_of::<usize>())?;
    if let Some(def) = work.at(&module.structs, id.as_usize())? {
        work.admit(1, size_of::<bool>())?;
        if def.id == id {
            return Ok(Some(def));
        }
    }
    let mut at = 0;
    while let Some(def) = work.at(&module.structs, at)? {
        work.admit(1, size_of::<bool>())?;
        if def.id == id {
            return Ok(Some(def));
        }
        work.next(&mut at)?;
    }
    Ok(None)
}
