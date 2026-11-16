// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn precise<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut n = 0;
        while let Some(row) = work.at(&module.structs, n)? {
            work.admit(2, size_of::<u32>() + size_of::<usize>())?;
            let id = row.id.index();
            let before = self.errors.len();
            work.admit(3, size_of::<Option<u64>>())?;
            if let Some(align) = row.align
                && (align == 0 || !align.is_power_of_two())
            {
                self.push(id, "align must be a non-zero power of two", work)?;
            }
            work.admit(6, 2 * size_of::<Option<u64>>())?;
            if let (Some(size), Some(align)) = (row.size, row.align)
                && align != 0
                && align.is_power_of_two()
                && size % align != 0
            {
                self.push(id, "size must be a multiple of align", work)?;
            }
            work.admit(1, size_of::<Option<u64>>())?;
            if let Some(size) = row.size {
                let mut f = 0;
                while let Some(field) = work.at(&row.fields, f)? {
                    work.admit(1, size_of::<Option<u64>>())?;
                    if let Some(offset) = field.offset {
                        work.admit(2, 0)?;
                        if offset > size
                            || (offset == size && !query::zero(self, module, &field.ty, work)?)
                        {
                            self.push(
                                id,
                                "field offset is outside the declared struct size",
                                work,
                            )?;
                            break;
                        }
                    }
                    work.next(&mut f)?;
                }
            }
            work.admit(1, 0)?;
            if self.errors.len() == before {
                self.overlap(row, id, work)?;
            }
            work.admit(4, size_of::<trust_ir::StructRepr>())?;
            let clamp = match row.repr {
                trust_ir::StructRepr::Packed(n) if n != 0 && n.is_power_of_two() => {
                    Some(u64::from(n))
                }
                trust_ir::StructRepr::Packed(_) => {
                    work.next(&mut n)?;
                    continue;
                }
                _ => None,
            };
            work.admit(2, size_of::<Option<u64>>())?;
            if let (Some(clamp), Some(align)) = (clamp, row.align)
                && align > clamp
            {
                self.push(id, "struct alignment exceeds the repr(packed) clamp", work)?;
                work.next(&mut n)?;
                continue;
            }
            let mut f = 0;
            while let Some(field) = work.at(&row.fields, f)? {
                work.admit(1, size_of::<Option<u64>>())?;
                let Some(offset) = field.offset else {
                    work.next(&mut f)?;
                    continue;
                };
                let natural = match self.query(&field.ty, work)? {
                    Some(summary) => {
                        work.admit(4, size_of::<Option<u64>>())?;
                        let Some(bits) = summary.align else {
                            work.next(&mut f)?;
                            continue;
                        };
                        if bits == 0 || !bits.is_multiple_of(8) {
                            work.next(&mut f)?;
                            continue;
                        }
                        bits / 8
                    }
                    None => {
                        if self.take_target(work)? {
                            self.target_error(id, work)?;
                            break;
                        }
                        work.next(&mut f)?;
                        continue;
                    }
                };
                work.admit(4, size_of::<u64>())?;
                let effective = clamp.map_or(natural, |c| natural.min(c));
                if effective != 0 && offset % effective != 0 {
                    self.push(
                        id,
                        "field offset is not a multiple of the field's effective alignment",
                        work,
                    )?;
                    break;
                }
                work.next(&mut f)?;
            }
            work.next(&mut n)?;
        }
        Ok(())
    }
    fn overlap<O: ExecutionObserver>(
        &mut self,
        row: &trust_ir::ty::StructDef,
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.ranges.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut f = 0;
        while let Some(field) = work.at(&row.fields, f)? {
            work.admit(1, size_of::<Option<u64>>())?;
            if let Some(offset) = field.offset {
                match self.query(&field.ty, work)? {
                    Some(Summary {
                        size: Some(size), ..
                    }) => {
                        work.reserve(&mut self.ranges)?;
                        work.admit(1, size_of::<(u64, u64)>())?;
                        self.ranges.push((offset, size));
                    }
                    Some(_) => {}
                    None => {
                        self.retire_error(work);
                        work.admit(1, 0)?;
                    }
                }
            }
            work.next(&mut f)?;
        }
        let mut left = 0;
        let mut found = false;
        while let Some(&(a, asize)) = work.at(&self.ranges, left)? {
            let mut right = left;
            work.next(&mut right)?;
            while let Some(&(b, bsize)) = work.at(&self.ranges, right)? {
                work.admit(16, 4 * size_of::<u64>())?;
                if byte_ranges_overlap(a, asize, b, bsize) {
                    found = true;
                    break;
                }
                work.next(&mut right)?;
            }
            if found {
                break;
            }
            work.next(&mut left)?;
        }
        retire_fixed(take(&mut self.ranges), work);
        work.admit(1, 0)?;
        if found {
            self.push(id, STRUCT_FIELDS_OVERLAP_REASON, work)?;
        }
        Ok(())
    }
}
