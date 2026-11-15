// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::consumption::{self, Direction, Fields};
use super::*;
impl State<'_> {
    fn field_prefix<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: u32,
        op: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.base(&function.name, Some(block), work)?;
        work.text(": ", &mut self.base_location)?;
        work.text(op, &mut self.base_location)
    }
    pub(super) fn field_write<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        flow: &Flow<'_>,
        block: u32,
        inst: &Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        match inst {
            Inst::InsertField {
                aggregate,
                field,
                value,
                ..
            } => {
                let Some(aggregate_ty) = flow.value(*aggregate, work)? else {
                    return Ok(());
                };
                self.field_prefix(function, block, "insert_field ", work)?;
                work.ty(aggregate_ty, &mut self.base_location)?;
                work.text(" field ", &mut self.base_location)?;
                work.number(*field as u128, &mut self.base_location)?;
                if let Some(fields) = consumption::fields(module, aggregate_ty, work)? {
                    if let Some(required) = fields.get(*field as usize, work)? {
                        self.value(module, flow, *value, required, work)?;
                    }
                } else if *field != 0
                    && let Some(actual) = flow.value(*value, work)?
                {
                    self.enum_consumption(
                        module,
                        aggregate_ty,
                        *field,
                        actual,
                        Some(flow.fact(value.index(), work)?),
                        &flow.facts,
                        Direction::Write,
                        work,
                    )?;
                }
            }
            Inst::InsertElement { array, value, .. } => {
                if let Some(array_ty) = flow.value(*array, work)?
                    && let Some(required) = consumption::element(module, array_ty, work)?
                {
                    self.field_prefix(function, block, "insert_element into ", work)?;
                    work.ty(array_ty, &mut self.base_location)?;
                    self.value(module, flow, *value, required, work)?;
                }
            }
            Inst::BindSlot { frame, slot, value } => {
                if let Some(i) = graph::find(&flow.frames, frame.index(), work)?
                    && let Some(required) = work.at(&flow.frames[i].1.slots, *slot as usize)?
                {
                    self.field_prefix(function, block, "bind_slot slot ", work)?;
                    work.number(*slot as u128, &mut self.base_location)?;
                    self.value(module, flow, *value, &required.ty, work)?;
                }
            }
            Inst::MakeAggregate {
                ty,
                variant,
                fields,
            } => {
                let lanes = match (ty, variant) {
                    (Ty::Enum(id), Some(v)) => match consumption::enumeration(module, *id, work)? {
                        Some(def) => work
                            .at(&def.variants, *v as usize)?
                            .map(|v| Fields::Plain(v.fields.as_slice())),
                        None => None,
                    },
                    (Ty::Array(..), None) => consumption::element(module, ty, work)?
                        .map(|t| Fields::Repeated(t, fields.len())),
                    (_, None) => consumption::fields(module, ty, work)?,
                    _ => None,
                };
                if let Some(lanes) = lanes {
                    for (i, field) in fields.iter().take(lanes.len()).enumerate() {
                        work.admit(1, 0)?;
                        let Some(required) = lanes.get(i, work)? else {
                            return Err(ObservedValueError::InvalidRange);
                        };
                        self.field_prefix(function, block, "make_aggregate ", work)?;
                        work.ty(ty, &mut self.base_location)?;
                        work.text(" lane ", &mut self.base_location)?;
                        work.number(i as u128, &mut self.base_location)?;
                        self.value(module, flow, *field, required, work)?;
                    }
                }
            }
            Inst::ArraySplat { ty, value } => {
                if let Some(required) = consumption::element(module, ty, work)? {
                    self.field_prefix(function, block, "array_splat ", work)?;
                    work.ty(ty, &mut self.base_location)?;
                    self.value(module, flow, *value, required, work)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    pub(super) fn field_read<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        flow: &Flow<'_>,
        block: u32,
        inst: &Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let (from_definition, demanded) = match inst {
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => {
                let Some(aggregate_ty) = flow.value(*aggregate, work)? else {
                    return Ok(());
                };
                let Some(fields) = consumption::fields(module, aggregate_ty, work)? else {
                    self.field_prefix(function, block, "extract_field ", work)?;
                    work.ty(aggregate_ty, &mut self.base_location)?;
                    work.text(" field ", &mut self.base_location)?;
                    work.number(*field as u128, &mut self.base_location)?;
                    self.enum_consumption(
                        module,
                        aggregate_ty,
                        *field,
                        ty,
                        None,
                        &flow.facts,
                        Direction::Read,
                        work,
                    )?;
                    return Ok(());
                };
                let Some(from) = fields.get(*field as usize, work)? else {
                    return Ok(());
                };
                self.field_prefix(function, block, "extract_field field ", work)?;
                work.number(*field as u128, &mut self.base_location)?;
                (from, ty)
            }
            Inst::ExtractElement { ty, array, .. } => {
                let Some(array_ty) = flow.value(*array, work)? else {
                    return Ok(());
                };
                let Some(from) = consumption::element(module, array_ty, work)? else {
                    return Ok(());
                };
                self.field_prefix(function, block, "extract_element", work)?;
                (from, ty)
            }
            Inst::LoadSlot { frame, slot, ty } => {
                let Some(i) = graph::find(&flow.frames, frame.index(), work)? else {
                    return Ok(());
                };
                let Some(from) = work.at(&flow.frames[i].1.slots, *slot as usize)? else {
                    return Ok(());
                };
                self.field_prefix(function, block, "load_slot slot ", work)?;
                work.number(*slot as u128, &mut self.base_location)?;
                (&from.ty, ty)
            }
            _ => return Ok(()),
        };
        self.consumption(
            module,
            from_definition,
            demanded,
            None,
            &flow.facts,
            Sink::Main,
            work,
        )
    }
}
