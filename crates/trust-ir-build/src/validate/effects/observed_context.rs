// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Fixed borrowed contexts only; no effect/body/authority admission.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_need::{Piece, Side};
use super::{Arg, AssertKind, EffectPlace, Module, PanicLocation, ValueId};
use core::mem::size_of;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod arguments;
mod labels;
mod storage;
#[cfg(test)]
mod tests;
pub(super) use labels::root_label_observed;
use storage::Work;
type R<T> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
pub(super) enum CallKind {
    Plain,
    Panic,
}
#[derive(Clone, Copy)]
pub(super) struct Call {
    pub(super) mnemonic: &'static str,
    pub(super) kind: CallKind,
}
#[derive(Clone, Copy)]
pub(super) enum What {
    Instruction(&'static str),
    Parameter { call: Call, side: Side, index: u32 },
}
#[derive(Clone, Copy)]
pub(super) enum Arguments<'i> {
    Values(&'i [ValueId]),
    ElementSlot,
    Panic {
        operands: Option<[ValueId; 2]>,
        location: PanicLocation,
    },
}
impl Call {
    pub(super) fn parts_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<[Piece<'static>; 2]> {
        let mut work = begin(
            session,
            site,
            2,
            size_of::<Self>() + size_of::<[Piece<'_>; 2]>(),
        )?;
        let suffix = match self.kind {
            CallKind::Plain => "",
            CallKind::Panic => " (its failure's panic call)",
        };
        let answer = [Piece::Text(self.mnemonic), Piece::Text(suffix)];
        work.publish(answer)
    }
}
impl What {
    pub(super) fn parts_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<[Piece<'static>; 7]> {
        let mut work = begin(
            session,
            site,
            3,
            size_of::<Self>() + size_of::<[Piece<'_>; 7]>(),
        )?;
        let answer = match self {
            What::Instruction(mnemonic) => [
                Piece::Text(mnemonic),
                Piece::Text(""),
                Piece::Text(""),
                Piece::Text(""),
                Piece::Text(""),
                Piece::Text(""),
                Piece::Text(""),
            ],
            What::Parameter { call, side, index } => {
                // Prepay transport before the child may return Copy headers.
                work.admit(1, size_of::<[Piece<'_>; 2]>())?;
                let [mnemonic, suffix] = call.parts_observed(work.session, work.site)?;
                work.admit(2, size_of::<Side>() + size_of::<u32>())?;
                let side = match side {
                    Side::Read => "reads",
                    Side::Write => "writes",
                };
                [
                    mnemonic,
                    suffix,
                    Piece::Text(" (callee "),
                    Piece::Text(side),
                    Piece::Text(" *param"),
                    Piece::U32(*index),
                    Piece::Text(")"),
                ]
            }
        };
        work.publish(answer)
    }
}
fn begin<'s, 'o, O: ExecutionObserver>(
    session: &'s mut ObservedSession<'o, O>,
    site: ExecutionSite,
    work: usize,
    copy_bytes: usize,
) -> R<Work<'s, 'o, O>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work,
        copy_bytes: copy_bytes + size_of::<Work<'_, '_, O>>(),
    })?;
    Ok(Work { session, site })
}
// Only fixed Copy arrays/scalars and borrowed headers are local/returned.
// No variable allocation, owned input disposal, label rendering, validation
// or owner/proof/native capability is performed here.
