// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::while_let_loop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn direct<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        layout: &EnumLayoutDescriptor,
        offset: u64,
        align: Option<u64>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(repr) = enm.canonical_tag_repr_observed(work.session, work.site)? else {
            return Ok(());
        };
        let size = lane_size(repr, work)?;
        if let Some(align) = align {
            work.admit(2, 2 * size_of::<u64>())?;
            if !offset.is_multiple_of(align) {
                work.admit(1, size_of::<[Part<'_>; 5]>())?;
                self.message(
                    enm,
                    &[
                        Part::Text("a direct tag aligned to "),
                        Part::Number(u128::from(align)),
                        Part::Text(" bytes"),
                    ],
                    &[Part::Text("tag_offset "), Part::Number(u128::from(offset))],
                    work,
                )?;
            }
            work.admit(1, 0)?;
            if align > layout.align {
                work.admit(1, size_of::<[Part<'_>; 4]>())?;
                self.message(
                    enm,
                    &[
                        Part::Text("descriptor align at least direct-tag alignment "),
                        Part::Number(u128::from(align)),
                    ],
                    &[Part::Text("align "), Part::Number(u128::from(layout.align))],
                    work,
                )?;
            }
        }
        work.admit(3, size_of::<Option<u64>>())?;
        if !offset
            .checked_add(size)
            .is_some_and(|end| end <= layout.size)
        {
            work.admit(1, size_of::<[Part<'_>; 7]>())?;
            self.message(
                enm,
                &[
                    Part::Text("a direct tag ("),
                    Part::Number(u128::from(size)),
                    Part::Text(" bytes) within size "),
                    Part::Number(u128::from(layout.size)),
                ],
                &[Part::Text("tag_offset "), Part::Number(u128::from(offset))],
                work,
            )?;
        }
        let mut index = 0;
        loop {
            let Some(variant) = work.at(&enm.variants, index)? else {
                break;
            };
            let Some(offsets) = work.at(&layout.variant_field_offsets, index)? else {
                break;
            };
            work.admit(1, 2 * size_of::<usize>())?;
            if offsets.len() == variant.fields.len() {
                let mut field = 0;
                while let Some(ty) = work.at(&variant.fields, field)? {
                    let field_offset = *work
                        .at(offsets, field)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    if let Some(field_size) = self.size(ty, work)? {
                        work.admit(12, 4 * size_of::<u64>())?;
                        if byte_ranges_overlap(offset, size, field_offset, field_size) {
                            work.admit(1, size_of::<[Part<'_>; 5]>())?;
                            self.message(
                                enm,
                                &[Part::Text("a direct tag disjoint from every non-ZST field")],
                                &[
                                    Part::Text("tag overlaps variant "),
                                    Part::Number(index as u128),
                                    Part::Text(" field "),
                                    Part::Number(field as u128),
                                ],
                                work,
                            )?;
                        }
                    }
                    work.next(&mut field)?;
                }
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
}
