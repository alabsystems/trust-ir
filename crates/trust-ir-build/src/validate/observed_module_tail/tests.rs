// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; full actual ordinary tail rules are separate complete oracles.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::ProofAnnotation;
use trust_ir::value::{ClosureTyId, FuncTyId};
use trust_ir::{Block, InstrNode};
mod custody;
mod parity;
mod stops;
#[derive(Clone, Copy)]
enum Rule {
    Casts,
    Facts,
}
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original module-tail stop");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(5101))
}
fn cast(op: CastOp, src: Ty, dst: Ty) -> InstrNode {
    InstrNode::new(Inst::Cast {
        op,
        src_ty: src,
        dst_ty: dst,
        operand: ValueId::new(0),
    })
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.func_types.push(FuncTy::unrecorded(vec![], vec![], false));
    let mut f = Function::new(FuncId::new(5101), "f", FuncTyId::new(0), BlockId::new(7));
    f.proofs = vec![
        ProofAnnotation::ValueRange {
            lo: i128::MAX,
            hi: i128::MIN,
        },
        ProofAnnotation::KnownBits {
            zeros: u128::MAX,
            ones: 1,
        },
    ];
    let mut b = Block::new(f.entry);
    b.body = vec![
        cast(CastOp::Transmute, Ty::U8, Ty::U64),
        cast(CastOp::Bitcast, Ty::Bool, Ty::U8),
        cast(CastOp::ReifyFnPointer, Ty::U64, Ty::Ptr),
    ];
    b.body[0].proofs = vec![
        ProofAnnotation::KnownBits { zeros: 5, ones: 3 },
        ProofAnnotation::ValueRange { lo: 2, hi: 1 },
    ];
    f.blocks.push(b);
    m.functions.push(f);
    m
}
fn custom() -> Module {
    let mut m = fixture();
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "unsupported-λ🦀".repeat(300),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    m.functions[0].blocks[0].body = vec![
        cast(CastOp::Bitcast, Ty::U8, Ty::U8),
        cast(CastOp::Transmute, Ty::U8, Ty::U8),
    ];
    m
}
fn original(m: &Module, rule: Rule) -> Vec<ValidationError> {
    match rule {
        Rule::Casts => super::super::validate_layout_sensitive_casts(&m.layout_table()),
        Rule::Facts => super::super::validate_value_facts(m),
    }
}
fn call<O: ExecutionObserver>(
    m: &Module,
    rule: Rule,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    match rule {
        Rule::Casts => validate_layout_sensitive_casts_observed(&m.layout_table(), s, site()),
        Rule::Facts => validate_value_facts_observed(m, s, site()),
    }
}
fn run(m: &Module, rule: Rule) -> (Vec<ValidationError>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(m, rule, &mut s).unwrap();
    let end = calls.get();
    assert_eq!(out, original(m, rule));
    let expected = out.clone();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, end)
}
fn state_run<O: ExecutionObserver>(
    state: &mut State,
    m: &Module,
    rule: Rule,
    w: &mut Work<'_, '_, O>,
) -> R {
    match rule {
        Rule::Casts => state.casts(&m.layout_table(), w),
        Rule::Facts => state.facts(m, w),
    }
}
fn drain<O: ExecutionObserver>(state: &mut State, w: &mut Work<'_, '_, O>) {
    state.retire_scratch(w);
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
fn empty(s: &State) {
    assert!(s.result.is_none());
    assert_eq!(
        s.op.capacity()
            + s.src.capacity()
            + s.dst.capacity()
            + s.reason.capacity()
            + s.errors.capacity(),
        0
    );
}
