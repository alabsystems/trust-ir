// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'_>,
        inst: &Inst,
        values: &ObservedValueTypes,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(12, size_of::<(&Ty, Option<u32>, &[ValueId])>())?;
        let Inst::MakeAggregate {
            ty,
            variant,
            fields,
        } = inst
        else {
            return Ok(());
        };
        let module = layouts.module();
        if let Ty::Enum(id) = ty {
            return self.enumeration(layouts, block, ty, *id, *variant, fields, values, work);
        }
        if variant.is_some() {
            return self.because(
                block,
                ty,
                "a `variant` index is only meaningful for an enum type",
                work,
            );
        }
        let lanes = match ty {
            Ty::Struct(id) => {
                let Some(def) = lookup::structure(module, *id, work)? else {
                    return self.because(
                        block,
                        ty,
                        "references an undefined struct definition",
                        work,
                    );
                };
                lanes::Lanes::Fields(&def.fields)
            }
            Ty::Record(id) => {
                let Some(def) = lookup::record(module, *id, work)? else {
                    return self.because(
                        block,
                        ty,
                        "references an undefined record definition",
                        work,
                    );
                };
                lanes::Lanes::Fields(&def.fields)
            }
            Ty::Tuple(types) => lanes::Lanes::Types(types),
            Ty::Array(element, len) => {
                let Some(expected) = work.at(&module.types, element.as_usize())? else {
                    return self.because(block, ty, "references an undefined element type", work);
                };
                work.admit(3, size_of::<Option<u64>>() + size_of::<bool>())?;
                if u64::try_from(fields.len()).ok() != Some(*len) {
                    work.unsigned(fields.len() as u128, &mut self.reason)?;
                    work.text(
                        " lane operand(s) supplied, but the array declares ",
                        &mut self.reason,
                    )?;
                    work.unsigned(u128::from(*len), &mut self.reason)?;
                    work.text(" element(s)", &mut self.reason)?;
                    return self.invalid(block, ty, work);
                }
                self.uniform(block, ty, fields, work)?;
                lanes::Lanes::Repeated(expected, fields.len())
            }
            _ => {
                return self.because(
                    block,
                    ty,
                    "not a type make_aggregate builds (struct, tuple, record, array or enum)",
                    work,
                );
            }
        };
        self.check(block, ty, fields, lanes, values, work)
    }
    fn uniform<O: ExecutionObserver>(
        &mut self,
        block: BlockId,
        ty: &Ty,
        fields: &[ValueId],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(first) = work.at(fields, 0)? else {
            return Ok(());
        };
        let mut at = 0;
        while let Some(field) = work.at(fields, at)? {
            work.admit(1, size_of::<bool>())?;
            if field != first {
                return Ok(());
            }
            work.next(&mut at)?;
        }
        self.location(block, ty, work)?;
        work.unsigned(fields.len() as u128, &mut self.spelling)?;
        work.text(" lane(s) that are all %", &mut self.spelling)?;
        work.unsigned(u128::from(first.index()), &mut self.spelling)?;
        work.text(" are spelled `array_splat ", &mut self.spelling)?;
        render::ty(ty, &mut self.render, &mut self.spelling, work)?;
        work.text(" %", &mut self.spelling)?;
        work.unsigned(u128::from(first.index()), &mut self.spelling)?;
        work.text("`", &mut self.spelling)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors.push(ValidationError::NonCanonicalUniformArray {
            location: take(&mut self.location),
            spelling: take(&mut self.spelling),
        });
        Ok(())
    }
}
