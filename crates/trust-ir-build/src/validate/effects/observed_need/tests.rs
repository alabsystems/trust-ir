// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; ordinary Side/flag own the exact first-reason oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::{Need as OrdinaryNeed, Side as OrdinarySide};
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::{BlockId, FuncId, GlobalId};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original Need stop");
        }
        if self.cleanup && e.phase == ExecutionPhase::ScratchRetirement {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(233))
}
fn p(index: u32) -> EffectPlace {
    EffectPlace::ParamPointee { index }
}
fn g(index: u32) -> EffectPlace {
    EffectPlace::Global(GlobalId::new(index))
}
fn text(pieces: &[Piece<'_>]) -> String {
    let mut out = String::new();
    for piece in pieces {
        match piece {
            Piece::Text(t) => out.push_str(t),
            Piece::U32(n) => out.push_str(&n.to_string()),
        }
    }
    out
}
#[derive(Clone, Copy)]
enum Op<'a> {
    Side(Side, Option<EffectPlace>, u32, &'a [Piece<'a>]),
    Flag(Flag, u32, &'a [Piece<'a>]),
}
impl Op<'_> {
    fn apply<O: ExecutionObserver>(
        self,
        n: &mut ObservedNeed,
        s: &mut ObservedSession<'_, O>,
    ) -> R {
        match self {
            Self::Side(side, p, b, pieces) => n.add_side_observed(side, p, b, pieces, s, site()),
            Self::Flag(flag, b, pieces) => n.add_flag_observed(flag, b, pieces, s, site()),
        }
    }
    fn ordinary(self, n: &mut OrdinaryNeed) {
        match self {
            Self::Side(side, p, b, pieces) => {
                let s = match side {
                    Side::Read => &mut n.reads,
                    Side::Write => &mut n.writes,
                };
                match p {
                    Some(p) => s.need(p, b, || text(pieces)),
                    None => s.force_everything(b, || text(pieces)),
                }
            }
            Self::Flag(flag, b, pieces) => {
                let slot = match flag {
                    Flag::Allocates => &mut n.allocates,
                    Flag::Frees => &mut n.frees,
                    Flag::MayUnwind => &mut n.may_unwind,
                    Flag::Io => &mut n.io,
                };
                super::super::flag(slot, b, || text(pieces))
            }
        }
    }
}
fn assert_side(a: &ObservedSide, b: &OrdinarySide) {
    assert_eq!(a.everything, b.everything);
    assert_eq!(
        a.places,
        b.places
            .iter()
            .map(|(p, r)| (*p, r.clone()))
            .collect::<Vec<_>>()
    );
}
fn assert_need(a: &ObservedNeed, b: &OrdinaryNeed) {
    assert_side(&a.reads, &b.reads);
    assert_side(&a.writes, &b.writes);
    assert_eq!(a.allocates, b.allocates);
    assert_eq!(a.frees, b.frees);
    assert_eq!(a.may_unwind, b.may_unwind);
    assert_eq!(a.io, b.io);
    assert_eq!(a.detail.capacity(), 0);
}
fn empty(n: &ObservedNeed) -> bool {
    n.detail.capacity() == 0
        && n.reads.everything.is_none()
        && n.writes.everything.is_none()
        && n.reads.places.capacity() == 0
        && n.writes.places.capacity() == 0
        && n.allocates.is_none()
        && n.frees.is_none()
        && n.may_unwind.is_none()
        && n.io.is_none()
}
fn trace(ops: &[Op<'_>]) -> (Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut n = ObservedNeed::new_observed(&mut s, site()).unwrap();
    let mut ordinary = OrdinaryNeed::default();
    for op in ops {
        op.apply(&mut n, &mut s).unwrap();
        op.ordinary(&mut ordinary);
        assert_need(&n, &ordinary);
    }
    let bound = calls.get();
    n.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (o, bound)
}
// A concrete fixture caller follows the production API's explicit obligation:
// once constructed, retain the whole Need and drain on every later error.
fn execute<O: ExecutionObserver>(ops: &[Op<'_>], s: &mut ObservedSession<'_, O>) -> R {
    let mut n = ObservedNeed::new_observed(s, site())?;
    let result = (|| -> R {
        for op in ops {
            op.apply(&mut n, s)?
        }
        Ok(())
    })();
    let cleanup = n.retire_observed(s, site());
    let result = result.and(cleanup);
    if s.first_refusal().is_some() {
        Err(ObservedValueError::AdmissionRefused)
    } else {
        result
    }
}
