// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Analysis<'_, '_> {
    pub(super) fn call<O: ExecutionObserver>(
        &mut self,
        callee: FuncId,
        args: Arguments<'_>,
        block: u32,
        call: Call,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            3,
            size_of::<Arguments<'_>>() + size_of::<Call>() + 11 * size_of::<Piece<'_>>(),
        )?;
        let Some(effects) =
            admissible_effects_observed(self.module, callee, self.policy, work.session, work.site)?
        else {
            let target = function_by_id_observed(self.module, callee, work.session, work.site)?;
            let prefix = call.parts_observed(work.session, work.site)?;
            work.admit(2, 6 * size_of::<Piece<'_>>())?;
            let label = match target {
                Some(f) => [Piece::Text("@"), Piece::Text(&f.name)],
                None => [Piece::Text("#"), Piece::U32(callee.index())],
            };
            return self.top(
                block,
                &[
                    prefix[0],
                    prefix[1],
                    Piece::Text(" to "),
                    label[0],
                    label[1],
                    Piece::Text(", which has no admissible effect summary (havoc)"),
                ],
                work,
            );
        };
        let target = function_by_id_observed(self.module, callee, work.session, work.site)?;
        work.admit(1, size_of::<bool>() + size_of::<usize>())?;
        let declaration = target.is_some_and(|f| f.blocks.is_empty());
        work.admit(2, 2 * size_of::<Side>())?;
        for side in [Side::Read, Side::Write] {
            work.admit(2, size_of::<&EffectSet>() + size_of::<&str>())?;
            let (set, side_name) = match side {
                Side::Read => (&effects.reads, "reads"),
                Side::Write => (&effects.writes, "writes"),
            };
            work.admit(3, size_of::<EffectPlace>())?;
            match set {
                EffectSet::Nothing => {}
                EffectSet::Everything => {
                    let prefix = call.parts_observed(work.session, work.site)?;
                    work.admit(1, 5 * size_of::<Piece<'_>>())?;
                    self.side(
                        side,
                        None,
                        block,
                        &[
                            prefix[0],
                            prefix[1],
                            Piece::Text(", whose callee "),
                            Piece::Text(side_name),
                            Piece::Text(" Everything"),
                        ],
                        work,
                    )?;
                }
                EffectSet::Places(places) => {
                    let mut at = 0usize;
                    while let Some(place) = work.at(places, at)? {
                        work.admit(2, size_of::<EffectPlace>() + size_of::<Option<Arg>>())?;
                        match place {
                            EffectPlace::ParamPointee { index } => {
                                let arg =
                                    args.get_observed(*index as usize, work.session, work.site)?;
                                work.admit(3, size_of::<Option<Arg>>())?;
                                match arg {
                                    Some(Arg::Value(value)) => self.access(
                                        side,
                                        value,
                                        block,
                                        What::Parameter {
                                            call,
                                            side,
                                            index: *index,
                                        },
                                        work,
                                    )?,
                                    Some(Arg::Global(global)) => {
                                        let prefix =
                                            call.parts_observed(work.session, work.site)?;
                                        let label = root_label_observed(
                                            EffectPlace::Global(global),
                                            self.module,
                                            work.session,
                                            work.site,
                                        )?;
                                        work.admit(1, 11 * size_of::<Piece<'_>>())?;
                                        self.side(
                                            side,
                                            Some(EffectPlace::Global(global)),
                                            block,
                                            &[
                                                prefix[0],
                                                prefix[1],
                                                Piece::Text(" (callee "),
                                                Piece::Text(side_name),
                                                Piece::Text(" *param"),
                                                Piece::U32(*index),
                                                Piece::Text(", which is "),
                                                label[0],
                                                label[1],
                                                label[2],
                                                Piece::Text(")"),
                                            ],
                                            work,
                                        )?;
                                    }
                                    Some(Arg::Untraceable) | None => {
                                        let prefix =
                                            call.parts_observed(work.session, work.site)?;
                                        work.admit(1, 7 * size_of::<Piece<'_>>())?;
                                        self.side(
                                            side,
                                            None,
                                            block,
                                            &[
                                                prefix[0],
                                                prefix[1],
                                                Piece::Text(" (callee "),
                                                Piece::Text(side_name),
                                                Piece::Text(" *param"),
                                                Piece::U32(*index),
                                                Piece::Text(
                                                    ", an argument this trace cannot follow)",
                                                ),
                                            ],
                                            work,
                                        )?;
                                    }
                                }
                            }
                            EffectPlace::Global(_) if declaration => {
                                let prefix = call.parts_observed(work.session, work.site)?;
                                work.admit(1, 3 * size_of::<Piece<'_>>())?;
                                self.side(side,None,block,&[prefix[0],prefix[1],Piece::Text(", whose declaration's summary names a global of another module")],work)?;
                            }
                            EffectPlace::Global(global) => {
                                let prefix = call.parts_observed(work.session, work.site)?;
                                let label = root_label_observed(
                                    *place,
                                    self.module,
                                    work.session,
                                    work.site,
                                )?;
                                work.admit(1, 9 * size_of::<Piece<'_>>())?;
                                self.side(
                                    side,
                                    Some(EffectPlace::Global(*global)),
                                    block,
                                    &[
                                        prefix[0],
                                        prefix[1],
                                        Piece::Text(" (callee "),
                                        Piece::Text(side_name),
                                        Piece::Text(" "),
                                        label[0],
                                        label[1],
                                        label[2],
                                        Piece::Text(")"),
                                    ],
                                    work,
                                )?;
                            }
                        }
                        work.next(&mut at)?;
                    }
                }
            }
        }
        // The ordinary call builds this fixed table before traversing it.
        work.admit(4, 4 * size_of::<(Flag, bool, &str)>())?;
        let flags = [
            (Flag::Allocates, effects.allocates, "allocates"),
            (Flag::Frees, effects.frees, "frees"),
            (Flag::MayUnwind, effects.may_unwind, "may unwind"),
            (Flag::Io, effects.io, "performs I/O"),
        ];
        for (flag, set, word) in flags {
            work.admit(1, size_of::<bool>())?;
            if set {
                let prefix = call.parts_observed(work.session, work.site)?;
                work.admit(1, 4 * size_of::<Piece<'_>>())?;
                self.flag(
                    flag,
                    block,
                    &[
                        prefix[0],
                        prefix[1],
                        Piece::Text(", whose callee "),
                        Piece::Text(word),
                    ],
                    work,
                )?;
            }
        }
        Ok(())
    }
    pub(super) fn panic_call<O: ExecutionObserver>(
        &mut self,
        kind: &AssertKind,
        site: &PanicSite,
        block: u32,
        mnemonic: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            2,
            size_of::<Arguments<'_>>() + size_of::<Call>() + size_of::<FuncId>(),
        )?;
        let args = Arguments::panic_observed(kind, site.location, work.session, work.site)?;
        self.call(
            site.entry,
            args,
            block,
            Call {
                mnemonic,
                kind: CallKind::Panic,
            },
            work,
        )
    }
}
