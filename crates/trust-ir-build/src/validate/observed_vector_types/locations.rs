// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn location<O: ExecutionObserver>(
        &mut self,
        location: Location<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        match location {
            Location::Type(i) => {
                work.text("type ty.", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
            }
            Location::SignatureParameter(i, p) => {
                work.text("functy.", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
                work.text(" param ", &mut self.location)?;
                work.number(p as u128, &mut self.location)?;
            }
            Location::SignatureReturn(i, p) => {
                work.text("functy.", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
                work.text(" return ", &mut self.location)?;
                work.number(p as u128, &mut self.location)?;
            }
            Location::Drop(i) => {
                work.text("drop_glue row ", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
            }
            Location::Global(name) => {
                work.text("global '", &mut self.location)?;
                work.text(name, &mut self.location)?;
                work.text("'", &mut self.location)?;
            }
            Location::Struct(name, field) => {
                work.text("struct @", &mut self.location)?;
                work.text(name, &mut self.location)?;
                work.text(" field '", &mut self.location)?;
                work.text(field, &mut self.location)?;
                work.text("'", &mut self.location)?;
            }
            Location::Record(name, field) => {
                work.text("record @", &mut self.location)?;
                work.text(name, &mut self.location)?;
                work.text(" field '", &mut self.location)?;
                work.text(field, &mut self.location)?;
                work.text("'", &mut self.location)?;
            }
            Location::Enum(name, variant, i) => {
                work.text("enum @", &mut self.location)?;
                work.text(name, &mut self.location)?;
                work.text(" variant '", &mut self.location)?;
                work.text(variant, &mut self.location)?;
                work.text("' field ", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
            }
            Location::Capture(i, c) => {
                work.text("closurety.", &mut self.location)?;
                work.number(i as u128, &mut self.location)?;
                work.text(" capture ", &mut self.location)?;
                work.number(c as u128, &mut self.location)?;
            }
        }
        Ok(())
    }
}
