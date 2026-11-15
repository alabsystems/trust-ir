// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn mask(raw: u128, bits: u32) -> u128 {
    if bits >= 128 {
        raw
    } else {
        raw & ((1u128 << bits) - 1)
    }
}
fn case_bits<O: ExecutionObserver>(
    width: u32,
    c: &Constant,
    w: &mut Work<'_, '_, O>,
) -> R<Option<u128>> {
    w.admit(8, size_of::<Option<u128>>())?;
    Ok(match c {
        Constant::Int(n) => Some(mask(*n as u128, width)),
        Constant::U128(n) => Some(mask(*n, width)),
        _ => None,
    })
}
fn contains<O: ExecutionObserver>(rows: &[u128], needle: u128, w: &mut Work<'_, '_, O>) -> R<bool> {
    let mut at = 0;
    while let Some(n) = w.at(rows, at)? {
        w.admit(2, size_of::<bool>())?;
        if *n == needle {
            return Ok(true);
        }
        w.next(&mut at)?;
    }
    Ok(false)
}
impl State<'_, '_> {
    fn bits<O: ExecutionObserver>(&self, disc: i128, tag: u32, w: &mut Work<'_, '_, O>) -> R<u128> {
        w.admit(8, 2 * size_of::<u128>() + size_of::<usize>())?;
        let mut bits = mask(disc as u128, tag);
        let mut at = self.widen.len();
        while at != 0 {
            w.admit(1, size_of::<usize>())?;
            at = at
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let step = w
                .at(&self.widen, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            w.admit(16, 3 * size_of::<u128>())?;
            bits = match *step {
                Widen::Zero { to } => mask(bits, to),
                Widen::Sign { from, to } => {
                    let negative = from > 0 && from < 128 && (bits >> (from - 1)) & 1 == 1;
                    let extended = if negative {
                        bits | !mask(u128::MAX, from)
                    } else {
                        bits
                    };
                    mask(extended, to)
                }
            };
        }
        Ok(bits)
    }
    fn refuse<O: ExecutionObserver>(&mut self, block: u32, w: &mut Work<'_, '_, O>) -> R {
        w.text(&self.enum_ty, &mut self.here)?;
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors
            .push(ValidationError::ExhaustiveSwitchCasesIncomplete {
                block,
                enum_ty: take(&mut self.here),
                reason: take(&mut self.reason),
            });
        Ok(())
    }
    pub(super) fn cases<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'_>,
        block: u32,
        cases: &[trust_ir::inst::SwitchCase],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<Selection<'_>>())?;
        let selected = self.selection.ok_or(ObservedValueError::InvalidRange)?;
        let def = selected.definition;
        let Some(values) = def.effective_discriminants_observed(w.session, w.site)? else {
            return Ok(());
        };
        self.discriminants = values;
        let Some(tag) = super::selector::tag_bits(def, w)? else {
            return Ok(());
        };
        let mut at = 0;
        while let Some(disc) = w.at(&self.discriminants, at)? {
            let bits = self.bits(*disc, tag, w)?;
            w.reserve(&mut self.disc_bits)?;
            w.admit(1, size_of::<u128>())?;
            self.disc_bits.push(bits);
            w.next(&mut at)?;
        }
        let mut at = 0;
        while let Some(case) = w.at(cases, at)? {
            let bits = case_bits(selected.width, &case.value, w)?;
            if let Some(bits) = bits
                && contains(&self.disc_bits, bits, w)?
            {
                if !contains(&self.covered, bits, w)? {
                    w.reserve(&mut self.covered)?;
                    w.admit(1, size_of::<u128>())?;
                    self.covered.push(bits);
                }
                w.next(&mut at)?;
                continue;
            }
            self.literal = case.value.display_observed(w.session, w.site)?;
            w.text("case value ", &mut self.reason)?;
            w.text(&self.literal, &mut self.reason)?;
            w.text(" is not a discriminant of ", &mut self.reason)?;
            w.text(&self.enum_ty, &mut self.reason)?;
            self.refuse(block, w)?;
            w.flat(take(&mut self.literal));
            w.admit(1, 0)?;
            w.next(&mut at)?;
        }
        let mut at = 0;
        let mut missing = false;
        while let Some(variant) = w.at(&def.variants, at)? {
            let disc = *w
                .at(&self.discriminants, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            let bits = *w
                .at(&self.disc_bits, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            if !contains(&self.covered, bits, w)?
                && !layouts.variant_is_uninhabited_observed(variant, w.session, w.site)?
            {
                if missing {
                    w.text(", ", &mut self.reason)?;
                } else {
                    w.text("no case for inhabited variant(s) {", &mut self.reason)?;
                    missing = true;
                }
                w.text(&variant.name, &mut self.reason)?;
                w.text(" = ", &mut self.reason)?;
                w.signed(disc, &mut self.reason)?;
            }
            w.next(&mut at)?;
        }
        if missing {
            w.text("}, so the default arm is reachable", &mut self.reason)?;
            self.refuse(block, w)?;
        }
        Ok(())
    }
}
