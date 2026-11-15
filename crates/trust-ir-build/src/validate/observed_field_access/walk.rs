// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        inst: &Inst,
        values: &ObservedValueTypes,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(16, size_of::<(Mode, &Ty, ValueId, u32)>())?;
        let (mode, declared, aggregate, field) = match inst {
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => (Mode::Extract, ty, *aggregate, *field),
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => (Mode::Insert(*value), ty, *aggregate, *field),
            _ => return Ok(()),
        };
        let Some(aggregate) = values.get_observed(aggregate, work.session, work.site)? else {
            return Ok(());
        };
        if matches!(mode, Mode::Insert(_))
            && !declared.structural_eq_observed(aggregate, work.session, work.site)?
        {
            // Exact result check is NOT refinement-deferred and always precedes
            // unknown definition/out-of-range/tag/unsupported-carrier refusal.
            self.mismatch(mode, block, "result", aggregate, declared, work)?;
        }
        if let Ty::Enum(id) = aggregate {
            let Some(def) = lookup::enumeration(module, *id, work)? else {
                return self.undefined(mode, block, aggregate, work);
            };
            return self.enumeration(mode, block, aggregate, def, field, declared, values, work);
        }
        work.admit(8, size_of::<Option<lanes::Lanes<'_>>>())?;
        let fields = match aggregate {
            Ty::Struct(id) => {
                lookup::structure(module, *id, work)?.map(|def| lanes::Lanes::Fields(&def.fields))
            }
            Ty::Record(id) => {
                lookup::record(module, *id, work)?.map(|def| lanes::Lanes::Fields(&def.fields))
            }
            Ty::Tuple(rows) => Some(lanes::Lanes::Types(rows)),
            Ty::Closure(id) => work
                .at(&module.closure_types, id.as_usize())?
                .map(|def| lanes::Lanes::Types(&def.captures)),
            _ => {
                work.text(
                    "aggregate operand must be a struct/record/tuple/enum/closure, got ",
                    &mut self.reason,
                )?;
                render::ty(aggregate, &mut self.render, &mut self.reason, work)?;
                return self.invalid(mode, block, work);
            }
        };
        let Some(fields) = fields else {
            return self.undefined(mode, block, aggregate, work);
        };
        let Some(expected) = fields.at(field as usize, work)? else {
            work.text("field index ", &mut self.reason)?;
            work.number(field as usize, &mut self.reason)?;
            work.text(" is out of range for ", &mut self.reason)?;
            render::ty(aggregate, &mut self.render, &mut self.reason, work)?;
            work.text(" (", &mut self.reason)?;
            let count = fields.len(work)?;
            work.number(count, &mut self.reason)?;
            work.text(" fields)", &mut self.reason)?;
            return self.invalid(mode, block, work);
        };
        match mode {
            Mode::Insert(value) => {
                if let Some(actual) = values.get_observed(value, work.session, work.site)? {
                    self.checked_mismatch(mode, block, "value", expected, actual, work)?;
                }
            }
            Mode::Extract => {
                self.checked_mismatch(mode, block, "field", expected, declared, work)?
            }
        }
        Ok(())
    }
}
