// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn layout<O: ExecutionObserver>(
    ty: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<Option<PointerLayoutShape>> {
    // Current shallow classifiers: eight pointer cases and five metadata
    // kinds, with only fixed Copy IDs/fields. No inline child or string walk.
    work.admit(16, size_of::<Option<PointerLayoutShape>>())?;
    Ok(ty.default_pointer_layout_shape())
}
pub(super) fn relative<O: ExecutionObserver>(
    src: &Ty,
    dst: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let from = layout(src, work)?;
    let to = layout(dst, work)?;
    match (from, to) {
        (Some(from), Some(to)) => {
            work.admit(2, 0)?;
            if from.lane_count() != to.lane_count() {
                return Ok(false);
            }
            // Option<PointerMetadataShape> is a fixed six-case Copy value:
            // SliceLen/VTable carry only one u32; no derived recursive Eq.
            work.admit(6, 0)?;
            Ok(from.metadata == to.metadata)
        }
        _ => Ok(false),
    }
}
pub(super) fn bitcast<O: ExecutionObserver>(
    src: &Ty,
    dst: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    // Both original tuple operands evaluate, even when source width is None.
    let from = src.bit_width_with_observed(DEFAULT_POINTER_BITS, work.session, work.site)?;
    let to = dst.bit_width_with_observed(DEFAULT_POINTER_BITS, work.session, work.site)?;
    match (from, to) {
        (Some(from), Some(to)) => {
            work.admit(1, 0)?;
            Ok(from == to)
        }
        _ => {
            let from = total(src, work)?;
            let to = total(dst, work)?;
            work.admit(1, 0)?;
            Ok(matches!((from, to), (Some(from), Some(to)) if from == to))
        }
    }
}
fn total<O: ExecutionObserver>(ty: &Ty, work: &mut Work<'_, '_, O>) -> R<Option<u32>> {
    match layout(ty, work)? {
        Some(layout) => {
            work.admit(2, size_of::<Option<u32>>())?;
            Ok(layout.total_bits())
        }
        None => Ok(None),
    }
}
