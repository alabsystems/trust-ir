// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Trace {
    pub(super) fn root<O: ExecutionObserver>(
        &mut self,
        root: Root,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(existing) = work.at(&self.output.rows, at)? {
            work.admit(8, 2 * size_of::<Root>())?;
            match compare(*existing, root) {
                CmpOrdering::Equal => return Ok(()),
                CmpOrdering::Greater => break,
                CmpOrdering::Less => work.next(&mut at)?,
            }
        }
        work.admit(1, size_of::<usize>())?;
        let mut position = self.output.rows.len();
        work.push(&mut self.output.rows, root)?;
        loop {
            work.admit(1, 0)?;
            if position <= at {
                return Ok(());
            }
            work.admit(2, 2 * size_of::<Root>() + size_of::<usize>())?;
            self.output.rows.swap(position, position - 1);
            position -= 1;
        }
    }
}
// Exhaustive current fixed scalar Root/EffectPlace order; no variable derived
// Ord/clone/sort is called behind a prewalk or aggregate charge.
fn compare(left: Root, right: Root) -> CmpOrdering {
    match left {
        Root::Local => match right {
            Root::Local => CmpOrdering::Equal,
            Root::Place(_) | Root::Untraceable => CmpOrdering::Less,
        },
        Root::Untraceable => match right {
            Root::Untraceable => CmpOrdering::Equal,
            Root::Local | Root::Place(_) => CmpOrdering::Greater,
        },
        Root::Place(left) => match right {
            Root::Local => CmpOrdering::Greater,
            Root::Untraceable => CmpOrdering::Less,
            Root::Place(right) => match (left, right) {
                (
                    EffectPlace::ParamPointee { index: a },
                    EffectPlace::ParamPointee { index: b },
                ) => a.cmp(&b),
                (EffectPlace::Global(a), EffectPlace::Global(b)) => a.index().cmp(&b.index()),
                (EffectPlace::ParamPointee { .. }, EffectPlace::Global(_)) => CmpOrdering::Less,
                (EffectPlace::Global(_), EffectPlace::ParamPointee { .. }) => CmpOrdering::Greater,
            },
        },
    }
}
