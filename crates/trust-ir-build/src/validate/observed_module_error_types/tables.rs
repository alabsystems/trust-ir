// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
enum Named {
    Struct,
    Record,
}
impl<'a> State<'a> {
    pub(super) fn tables<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut i = 0;
        while i < module.types.len() {
            work.surface()?;
            self.surface(Location::Type(i), &module.types[i], work)?;
            i += 1;
        }
        self.signatures(module, work)?;
        i = 0;
        while i < module.drop_glue.len() {
            work.surface()?;
            self.surface(Location::Drop(i), &module.drop_glue[i].ty, work)?;
            i += 1;
        }
        self.globals(module, work)
    }

    fn signatures<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut i = 0;
        while i < module.func_types.len() {
            work.admit(1, 0)?;
            let signature = &module.func_types[i];
            let mut j = 0;
            while j < signature.params.len() {
                work.surface()?;
                self.surface(
                    Location::SignatureParameter(i, j),
                    &signature.params[j],
                    work,
                )?;
                j += 1;
            }
            j = 0;
            while j < signature.returns.len() {
                work.surface()?;
                self.surface(Location::SignatureReturn(i, j), &signature.returns[j], work)?;
                j += 1;
            }
            i += 1;
        }
        Ok(())
    }

    fn globals<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut i = 0;
        while i < module.globals.len() {
            work.surface()?;
            let global = &module.globals[i];
            self.surface(Location::Global(&global.name), &global.ty, work)?;
            work.admit(1, 0)?;
            if let Some(align) = global.align
                && (align == 0 || !align.is_power_of_two())
            {
                self.alignment(&global.name, align, work)?;
            }
            i += 1;
        }
        Ok(())
    }

    pub(super) fn aggregates<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut i = 0;
        while i < module.structs.len() {
            work.admit(1, 0)?;
            let value = &module.structs[i];
            self.fields(Named::Struct, &value.name, &value.fields, work)?;
            i += 1;
        }
        i = 0;
        while i < module.records.len() {
            work.admit(1, 0)?;
            let value = &module.records[i];
            self.fields(Named::Record, &value.name, &value.fields, work)?;
            i += 1;
        }
        self.enums(module, work)?;
        self.captures(module, work)
    }

    fn fields<O: ExecutionObserver>(
        &mut self,
        kind: Named,
        name: &str,
        fields: &'a [trust_ir::ty::FieldDef],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut i = 0;
        while i < fields.len() {
            work.surface()?;
            let field = &fields[i];
            let location = match kind {
                Named::Struct => Location::Struct(name, &field.name),
                Named::Record => Location::Record(name, &field.name),
            };
            self.surface(location, &field.ty, work)?;
            i += 1;
        }
        Ok(())
    }

    fn enums<O: ExecutionObserver>(&mut self, module: &'a Module, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        let mut i = 0;
        while i < module.enums.len() {
            work.admit(1, 0)?;
            let enm = &module.enums[i];
            let mut j = 0;
            while j < enm.variants.len() {
                work.admit(1, 0)?;
                let variant = &enm.variants[j];
                let mut k = 0;
                while k < variant.fields.len() {
                    work.surface()?;
                    self.surface(
                        Location::Enum(&enm.name, &variant.name, k),
                        &variant.fields[k],
                        work,
                    )?;
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
        Ok(())
    }

    fn captures<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut i = 0;
        while i < module.closure_types.len() {
            work.admit(1, 0)?;
            let closure = &module.closure_types[i];
            let mut j = 0;
            while j < closure.captures.len() {
                work.surface()?;
                self.surface(Location::Capture(i, j), &closure.captures[j], work)?;
                j += 1;
            }
            i += 1;
        }
        Ok(())
    }
}
