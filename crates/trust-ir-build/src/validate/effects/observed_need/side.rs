// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl ObservedNeed {
    fn side(&self, side: Side) -> &ObservedSide {
        match side {
            Side::Read => &self.reads,
            Side::Write => &self.writes,
        }
    }
    fn side_mut(&mut self, side: Side) -> &mut ObservedSide {
        match side {
            Side::Read => &mut self.reads,
            Side::Write => &mut self.writes,
        }
    }
    /// None is Everything; a named place remains independent of Everything,
    /// just as the ordinary Side still records places after top is known.
    pub(in super::super) fn add_side_observed<O: ExecutionObserver>(
        &mut self,
        side: Side,
        place: Option<EffectPlace>,
        block: u32,
        pieces: &[Piece<'_>],
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.admit(
            2,
            size_of::<Side>()
                + size_of::<Option<EffectPlace>>()
                + size_of::<&[Piece<'_>]>()
                + size_of::<Work<'_, '_, O>>(),
        )?;
        self.begin(&mut work)?;
        work.admit(1, size_of::<Option<&Reason>>())?;
        match place {
            None if self.side(side).everything.is_some() => return work.publication(0),
            None => {
                self.render(pieces, &mut work)?;
                work.admit(2, size_of::<Reason>() + size_of::<Option<Reason>>())?;
                let reason = (block, take(&mut self.detail));
                self.side_mut(side).everything = Some(reason);
            }
            Some(place) => {
                let (found, at) = find(&self.side(side).places, place, &mut work)?;
                if found {
                    return work.publication(0);
                }
                self.render(pieces, &mut work)?;
                work.reserve(&mut self.side_mut(side).places)?;
                work.admit(2, size_of::<PlaceReason>() + size_of::<usize>())?;
                let reason = (block, take(&mut self.detail));
                let rows = &mut self.side_mut(side).places;
                let mut position = rows.len();
                rows.push((place, reason));
                loop {
                    work.admit(1, 0)?;
                    if position <= at {
                        break;
                    }
                    work.admit(2, 2 * size_of::<PlaceReason>() + size_of::<usize>())?;
                    rows.swap(position, position - 1);
                    position -= 1;
                }
            }
        }
        work.publication(0)
    }
}
fn find<O: ExecutionObserver>(
    rows: &[PlaceReason],
    place: EffectPlace,
    work: &mut Work<'_, '_, O>,
) -> R<(bool, usize)> {
    work.admit(1, size_of::<usize>())?;
    let mut at = 0usize;
    loop {
        work.admit(1, size_of::<Option<&PlaceReason>>())?;
        let Some((current, _)) = rows.get(at) else {
            return Ok((false, at));
        };
        work.admit(4, 2 * size_of::<EffectPlace>() + size_of::<Ordering>())?;
        match compare(*current, place) {
            Ordering::Equal => return Ok((true, at)),
            Ordering::Greater => return Ok((false, at)),
            Ordering::Less => work.next(&mut at)?,
        }
    }
}
fn compare(a: EffectPlace, b: EffectPlace) -> Ordering {
    match (a, b) {
        (EffectPlace::ParamPointee { index: a }, EffectPlace::ParamPointee { index: b }) => {
            a.cmp(&b)
        }
        (EffectPlace::Global(a), EffectPlace::Global(b)) => a.index().cmp(&b.index()),
        (EffectPlace::ParamPointee { .. }, EffectPlace::Global(_)) => Ordering::Less,
        (EffectPlace::Global(_), EffectPlace::ParamPointee { .. }) => Ordering::Greater,
    }
}
