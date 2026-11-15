// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
/// Exact ordinary direct-index root label, returned as borrowed recipe only.
/// A raw global name has no id/uniqueness/validity obligation added here.
pub(in super::super) fn root_label_observed<'m, O: ExecutionObserver>(
    place: EffectPlace,
    module: &'m Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<[Piece<'m>; 3]> {
    let mut work = begin(
        session,
        site,
        2,
        size_of::<EffectPlace>() + size_of::<&Module>() + size_of::<[Piece<'_>; 3]>(),
    )?;
    let answer = match place {
        EffectPlace::ParamPointee { index } => {
            [Piece::Text("*param"), Piece::U32(index), Piece::Text("")]
        }
        EffectPlace::Global(global) => {
            work.admit(
                1,
                size_of::<usize>() + size_of::<Option<&trust_ir::Global>>(),
            )?;
            match module.globals.get(global.as_usize()) {
                Some(target) => {
                    work.admit(1, size_of::<&str>())?;
                    [
                        Piece::Text("@"),
                        Piece::Text(target.name.as_str()),
                        Piece::Text(""),
                    ]
                }
                None => [
                    Piece::Text("global #"),
                    Piece::U32(global.index()),
                    Piece::Text(""),
                ],
            }
        }
    };
    work.publish(answer)
}
