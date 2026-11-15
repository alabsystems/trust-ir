// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn niche<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        layout: &EnumLayoutDescriptor,
        niche: Niche,
        align: Option<u64>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, size_of::<Option<u32>>())?;
        let count = u32::try_from(enm.variants.len()).ok();
        if count.is_none() || count.is_some_and(|count| niche.untagged >= count) {
            work.admit(1, size_of::<[Part<'_>; 3]>())?;
            self.message(
                enm,
                &[Part::Text("an in-range untagged variant")],
                &[
                    Part::Text("untagged_variant "),
                    Part::Number(u128::from(niche.untagged)),
                ],
                work,
            )?;
        }
        work.admit(3, size_of::<bool>())?;
        let in_range = niche.start <= niche.end && count.is_some_and(|count| niche.end < count);
        if !in_range {
            work.admit(1, size_of::<[Part<'_>; 4]>())?;
            self.message(
                enm,
                &[Part::Text("an ordered, in-range niche variant interval")],
                &[
                    Part::Number(u128::from(niche.start)),
                    Part::Text("..="),
                    Part::Number(u128::from(niche.end)),
                ],
                work,
            )?;
        }
        if count.is_some() {
            self.coverage(enm, niche, work)?;
        }
        let size = lane_size(niche.repr, work)?;
        if let Some(align) = align {
            work.admit(2, 0)?;
            if !niche.offset.is_multiple_of(align) {
                work.admit(1, size_of::<[Part<'_>; 5]>())?;
                self.message(
                    enm,
                    &[
                        Part::Text("a niche lane aligned to "),
                        Part::Number(u128::from(align)),
                        Part::Text(" bytes"),
                    ],
                    &[
                        Part::Text("niche_offset "),
                        Part::Number(u128::from(niche.offset)),
                    ],
                    work,
                )?;
            }
            work.admit(1, 0)?;
            if align > layout.align {
                work.admit(1, size_of::<[Part<'_>; 4]>())?;
                self.message(
                    enm,
                    &[
                        Part::Text("descriptor align at least niche alignment "),
                        Part::Number(u128::from(align)),
                    ],
                    &[Part::Text("align "), Part::Number(u128::from(layout.align))],
                    work,
                )?;
            }
        }
        work.admit(3, size_of::<Option<u64>>())?;
        let end = niche.offset.checked_add(size);
        if end.is_none_or(|end| end > layout.size) {
            work.admit(1, size_of::<[Part<'_>; 6]>())?;
            self.message(
                enm,
                &[
                    Part::Text("a niche lane ("),
                    Part::Number(u128::from(size)),
                    Part::Text(" bytes) within size "),
                    Part::Number(u128::from(layout.size)),
                ],
                &[
                    Part::Text("niche_offset "),
                    Part::Number(u128::from(niche.offset)),
                ],
                work,
            )?;
        }
        self.covering_field(enm, layout, niche, end, work)?;
        if in_range {
            self.niche_fields(enm, layout, niche, size, work)?;
        }
        self.capacity(enm, niche, size, work)
    }
    fn coverage<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        niche: Niche,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(variant) = work.at(&enm.variants, index)? {
            work.admit(5, size_of::<Option<u32>>() + size_of::<bool>())?;
            let encoded = u32::try_from(index).is_ok_and(|index| {
                index == niche.untagged || (niche.start <= index && index <= niche.end)
            });
            if !encoded && !self.uninhabited(variant, work)? {
                work.admit(1, size_of::<[Part<'_>; 11]>())?;
                self.message(enm,&[Part::Text("the niche interval plus the untagged variant to cover every inhabited variant")],
                    &[Part::Text("inhabited variant "),Part::Number(index as u128),Part::Text(" ("),Part::Text(&variant.name),
                        Part::Text(") is neither untagged "),Part::Number(u128::from(niche.untagged)),Part::Text(" nor in niche interval "),
                        Part::Number(u128::from(niche.start)),Part::Text("..="),Part::Number(u128::from(niche.end))],work)?;
                break;
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    fn capacity<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        niche: Niche,
        size: u64,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(8, 2 * size_of::<u128>() + size_of::<u32>())?;
        let bits = (size * 8) as u32;
        let max = if bits == 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        if niche.value > max {
            work.admit(1, size_of::<[Part<'_>; 5]>())?;
            self.message(
                enm,
                &[
                    Part::Text("niche_start representable in "),
                    Part::Number(u128::from(bits)),
                    Part::Text(" bits"),
                ],
                &[Part::Text("niche_start "), Part::Number(niche.value)],
                work,
            )?;
        }
        work.admit(3, size_of::<Option<u128>>())?;
        let span = niche.end.checked_sub(niche.start).map(u128::from);
        if span.is_none_or(|span| span > max) {
            work.admit(1, size_of::<[Part<'_>; 7]>())?;
            // Same rejection as ordinary corrected diagnostic; 2^128 cannot
            // be represented by u128. Never wrap the advertised capacity.
            match max.checked_add(1) {
                Some(capacity) => self.message(
                    enm,
                    &[
                        Part::Text("at most "),
                        Part::Number(capacity),
                        Part::Text(" distinct niche variants"),
                    ],
                    &[
                        Part::Text("niche interval "),
                        Part::Number(u128::from(niche.start)),
                        Part::Text("..="),
                        Part::Number(u128::from(niche.end)),
                    ],
                    work,
                )?,
                None => self.message(
                    enm,
                    &[Part::Text(
                        "at most 340282366920938463463374607431768211456 distinct niche variants",
                    )],
                    &[
                        Part::Text("niche interval "),
                        Part::Number(u128::from(niche.start)),
                        Part::Text("..="),
                        Part::Number(u128::from(niche.end)),
                    ],
                    work,
                )?,
            }
        }
        Ok(())
    }
}
