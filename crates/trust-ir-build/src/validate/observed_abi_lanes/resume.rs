// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn sum<O: ExecutionObserver>(
        &mut self,
        fields: Fields<'a>,
        owner: Owner,
        w: &mut Work<'_, '_, O>,
    ) -> R<Action<'a>> {
        let Some(first) = fields.at(0, w)? else {
            return Ok(Action::Summed(owner, Some(0)));
        };
        w.push(
            &mut self.frames,
            Frame::Sum {
                fields,
                next: 1,
                lanes: 0,
                owner,
            },
        )?;
        Ok(Action::Enter(first))
    }
    pub(super) fn next_variant<O: ExecutionObserver>(
        &mut self,
        memo: &mut ObservedAbiLanes<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R<Action<'a>> {
        w.admit(1, size_of::<Option<Frame<'_>>>())?;
        let Some(Frame::Enum {
            id,
            def,
            rule,
            counted,
        }) = self.frames.last().copied()
        else {
            return Err(ObservedValueError::InvalidRange);
        };
        w.admit(16, 4 * size_of::<usize>())?;
        let index = match rule {
            Rule::Untagged { variant } => (counted == 0).then_some(variant),
            Rule::Direct { .. } => (counted < def.variants.len()).then_some(counted),
            Rule::Niche { dataful } => {
                let others = def
                    .variants
                    .len()
                    .checked_sub(usize::from(dataful < def.variants.len()))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                if counted < others {
                    Some(if counted >= dataful {
                        counted
                            .checked_add(1)
                            .ok_or(ObservedValueError::CapacityOverflow)?
                    } else {
                        counted
                    })
                } else if counted == others {
                    Some(dataful)
                } else {
                    None
                }
            }
        };
        if let Some(index) = index {
            if let Some(variant) = w.at(&def.variants, index)? {
                return Ok(Action::Sum(Fields::Types(&variant.fields), Owner::Variant));
            }
            w.admit(1, size_of::<Option<Frame<'_>>>())?;
            self.frames.pop();
            memo.write(Node::Enum(id), Slot::Counted(None), w)?;
            return Ok(Action::Return(None));
        }
        w.admit(1, size_of::<Option<Frame<'_>>>())?;
        self.frames.pop();
        let count = match rule {
            Rule::Untagged { .. } | Rule::Niche { .. } => None,
            Rule::Direct { widest } => Some(
                widest
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            ),
        };
        memo.write(Node::Enum(id), Slot::Counted(count), w)?;
        Ok(Action::Return(count))
    }
    pub(super) fn resume<O: ExecutionObserver>(
        &mut self,
        _memo: &mut ObservedAbiLanes<'_>,
        count: Option<usize>,
        w: &mut Work<'_, '_, O>,
    ) -> R<Action<'a>> {
        w.admit(1, size_of::<Option<Frame<'_>>>())?;
        let Some(Frame::Sum {
            fields,
            next,
            lanes,
            owner,
        }) = self.frames.last().copied()
        else {
            return Err(ObservedValueError::InvalidRange);
        };
        w.admit(3, size_of::<Option<usize>>())?;
        let total = count.and_then(|count| lanes.checked_add(count));
        let field = fields.at(next, w)?;
        if let (Some(total), Some(field)) = (total, field) {
            w.admit(1, size_of::<Frame<'_>>())?;
            let Some(last) = self.frames.last_mut() else {
                return Err(ObservedValueError::InvalidRange);
            };
            *last = Frame::Sum {
                fields,
                next: next
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                lanes: total,
                owner,
            };
            return Ok(Action::Enter(field));
        }
        w.admit(1, size_of::<Option<Frame<'_>>>())?;
        self.frames.pop();
        Ok(Action::Summed(owner, total))
    }
    pub(super) fn summed<O: ExecutionObserver>(
        &mut self,
        memo: &mut ObservedAbiLanes<'_>,
        owner: Owner,
        total: Option<usize>,
        w: &mut Work<'_, '_, O>,
    ) -> R<Action<'a>> {
        w.admit(4, 0)?;
        match owner {
            Owner::Inline => Ok(Action::Return(total)),
            Owner::Struct(id) => {
                memo.write(Node::Struct(id), Slot::Counted(total), w)?;
                Ok(Action::Return(total))
            }
            Owner::Variant => self.variant_counted(memo, total, w),
        }
    }
    fn variant_counted<O: ExecutionObserver>(
        &mut self,
        memo: &mut ObservedAbiLanes<'_>,
        lanes: Option<usize>,
        w: &mut Work<'_, '_, O>,
    ) -> R<Action<'a>> {
        w.admit(1, size_of::<Option<Frame<'_>>>())?;
        let Some(Frame::Enum {
            id,
            def,
            mut rule,
            counted,
        }) = self.frames.last().copied()
        else {
            return Err(ObservedValueError::InvalidRange);
        };
        w.admit(16, 4 * size_of::<usize>())?;
        let counted = counted
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let length = match rule {
            Rule::Untagged { .. } => 1,
            Rule::Direct { .. } => def.variants.len(),
            Rule::Niche { dataful } => def
                .variants
                .len()
                .checked_add(usize::from(dataful >= def.variants.len()))
                .ok_or(ObservedValueError::CapacityOverflow)?,
        };
        let last = counted == length;
        let decided: Option<Option<usize>> = match (&mut rule, lanes) {
            (_, None) => Some(None),
            (Rule::Untagged { .. }, lanes) => Some(lanes),
            (Rule::Niche { .. }, lanes) if last => Some(lanes),
            (Rule::Niche { .. }, Some(0)) => None,
            (Rule::Niche { .. }, Some(_)) => Some(None),
            (Rule::Direct { .. }, Some(lanes)) if lanes > 1 => Some(None),
            (Rule::Direct { widest }, Some(lanes)) => {
                *widest = (*widest).max(lanes);
                None
            }
        };
        w.admit(1, size_of::<Frame<'_>>())?;
        match decided {
            Some(count) => {
                self.frames.pop();
                memo.write(Node::Enum(id), Slot::Counted(count), w)?;
                Ok(Action::Return(count))
            }
            None => {
                let Some(frame) = self.frames.last_mut() else {
                    return Err(ObservedValueError::InvalidRange);
                };
                *frame = Frame::Enum {
                    id,
                    def,
                    rule,
                    counted,
                };
                Ok(Action::NextVariant)
            }
        }
    }
}
