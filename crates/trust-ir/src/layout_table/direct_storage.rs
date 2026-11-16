// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source deadness and physical storage are separate facts. These checks
//! authorize no source or proof; they validate an enclosing Direct image.

use super::*;
use crate::ty::{EnumLayoutDescriptor, EnumVariant, UninhabitedVariantLayout};

#[cfg(test)]
pub(crate) mod tests;

pub(crate) trait Work {
    type Error;
    fn poll(&mut self) -> Result<(), Self::Error>;
    fn references(&mut self, module: &Module, def: &EnumDef) -> Result<bool, Self::Error>;
    fn dead(&mut self, module: &Module, variant: &EnumVariant) -> Result<bool, Self::Error>;
}

pub(crate) struct Ordinary<'a> {
    pub(crate) inhabit: &'a mut InhabitMemo,
    pub(crate) function_item: &'a dyn Fn(crate::FuncId) -> bool,
}

impl Work for Ordinary<'_> {
    type Error = core::convert::Infallible;
    fn poll(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn references(&mut self, module: &Module, def: &EnumDef) -> Result<bool, Self::Error> {
        Ok(super::references::valid_with(
            module,
            def.variants.iter().flat_map(|row| &row.fields),
            self.function_item,
        ))
    }
    fn dead(&mut self, module: &Module, variant: &EnumVariant) -> Result<bool, Self::Error> {
        Ok(self.inhabit.variant_is_uninhabited(module, variant))
    }
}

pub(crate) fn profile(def: &EnumDef, variant: usize) -> Option<&UninhabitedVariantLayout> {
    let EnumTagEncoding::DirectWithUninhabited { variants, .. } = &def.layout.as_ref()?.encoding
    else {
        return None;
    };
    let variant = u32::try_from(variant).ok()?;
    variants
        .binary_search_by_key(&variant, |row| row.variant)
        .ok()
        .map(|index| &variants[index])
}

/// Two fixed operations per comparison, with at most ceil(log2(count)) + 1
/// comparisons. The empty search makes no comparison. The bound is at most
/// 2 * (usize::BITS + 1), so this arithmetic cannot overflow usize.
pub(crate) fn profile_lookup_work(count: usize) -> usize {
    if count == 0 {
        0
    } else {
        2 * ((usize::BITS - (count - 1).leading_zeros()) as usize + 1)
    }
}

/// All validation precedes any dead field's value-layout query. Offsets have
/// one authority: the enclosing descriptor's original source-indexed rows.
pub(crate) fn validate<W: Work>(
    module: &Module,
    def: &EnumDef,
    desc: &EnumLayoutDescriptor,
    tag_size: u64,
    tag_align: u64,
    work: &mut W,
) -> Result<bool, W::Error> {
    let EnumTagEncoding::DirectWithUninhabited {
        tag_offset,
        variants,
    } = &desc.encoding
    else {
        return Ok(false);
    };
    work.poll()?;
    if !work.references(module, def)? {
        return Ok(false);
    }
    if desc.align == 0
        || !desc.align.is_power_of_two()
        || !desc.size.is_multiple_of(desc.align)
        || desc.variant_field_offsets.len() != def.variants.len()
        || desc.size.checked_mul(8).is_none()
        || desc.align.checked_mul(8).is_none()
    {
        return Ok(false);
    }
    let mut previous = None;
    for row in variants {
        work.poll()?;
        if previous.is_some_and(|index| index >= row.variant)
            || row.variant as usize >= def.variants.len()
        {
            return Ok(false);
        }
        previous = Some(row.variant);
    }
    let mut next = 0;
    for (index, variant) in def.variants.iter().enumerate() {
        work.poll()?;
        let profiled = variants
            .get(next)
            .is_some_and(|row| row.variant as usize == index);
        if work.dead(module, variant)? != profiled {
            return Ok(false);
        }
        if profiled {
            next += 1;
        }
    }
    if next != variants.len() {
        return Ok(false);
    }
    for row in variants {
        work.poll()?;
        let source = &def.variants[row.variant as usize];
        let offsets = &desc.variant_field_offsets[row.variant as usize];
        if row.align == 0
            || !row.align.is_power_of_two()
            || !row.size.is_multiple_of(row.align)
            || row.align > desc.align
            || !desc.align.is_multiple_of(row.align)
            || row.size > desc.size
            || row.fields.len() != source.fields.len()
            || offsets.len() != source.fields.len()
            || tag_align == 0
            || tag_align > row.align
            || !tag_offset.is_multiple_of(tag_align)
            || tag_offset
                .checked_add(tag_size)
                .is_none_or(|end| end > row.size)
        {
            return Ok(false);
        }
        for (index, field) in row.fields.iter().enumerate() {
            work.poll()?;
            let offset = offsets[index];
            if field.align == 0
                || !field.align.is_power_of_two()
                || !field.size.is_multiple_of(field.align)
                || field.align > row.align
                || !offset.is_multiple_of(field.align)
                || offset
                    .checked_add(field.size)
                    .is_none_or(|end| end > row.size)
                || byte_ranges_overlap(*tag_offset, tag_size, offset, field.size)
            {
                return Ok(false);
            }
            for later in index + 1..row.fields.len() {
                work.poll()?;
                if byte_ranges_overlap(offset, field.size, offsets[later], row.fields[later].size) {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}
