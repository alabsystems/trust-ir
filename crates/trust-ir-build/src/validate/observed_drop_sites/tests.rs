// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Twenty authored UNRUN controls; exact ordinary drop-site pass is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::{AssertKind, PanicLocation, PanicSite};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::{BlockId, FuncId, FuncTyId, PredId, StructId, TyId, ValueId};
use trust_ir::{Block, CallingConv, DropGlueEntry, InstrNode};
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
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup_after: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original drop-site stop");
        }
        if self.cleanup_after.is_some_and(|n| self.events.len() > n)
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
    ExecutionSite::Entry(FuncId::new(379))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn module(insts: Vec<Inst>) -> Module {
    let mut m = Module::new("drop sites");
    let mut f = Function::new(
        FuncId::new(11),
        "dropλ\0",
        FuncTyId::new(0),
        BlockId::new(7),
    );
    let mut b = Block::new(BlockId::new(7));
    b.body = insts.into_iter().map(InstrNode::new).collect();
    f.blocks.push(b);
    m.functions.push(f);
    m
}
fn drop_inst(ty: Ty, invoke: bool) -> Inst {
    if invoke {
        Inst::DropInvoke {
            ty,
            ptr: v(1),
            normal_dest: BlockId::new(8),
            normal_args: vec![],
            unwind_dest: BlockId::new(9),
        }
    } else {
        Inst::Drop { ty, ptr: v(1) }
    }
}
fn direct(callee: u32, kind: usize) -> Inst {
    let callee = FuncId::new(callee);
    let site = PanicSite {
        entry: callee,
        location: PanicLocation::Value(v(1)),
    };
    match kind {
        0 => Inst::Call {
            callee,
            args: vec![],
        },
        1 => Inst::CallCannotUnwind {
            callee,
            args: vec![],
        },
        2 => Inst::Invoke {
            callee,
            args: vec![],
            normal_dest: BlockId::new(8),
            normal_args: vec![],
            unwind_dest: BlockId::new(9),
        },
        3 => Inst::SeqMap {
            ty: Ty::Sequence(TyId::new(0)),
            seq: v(1),
            fwd: callee,
        },
        4 => Inst::Assert {
            cond: v(1),
            kind: AssertKind::NullPtr,
            site: Some(site),
        },
        5 => Inst::AssertInvoke {
            cond: v(1),
            kind: AssertKind::DivByZero,
            site,
            normal_dest: BlockId::new(8),
            normal_args: vec![],
            unwind_dest: BlockId::new(9),
        },
        _ => unreachable!("six explicit fixture kinds"),
    }
}
fn register(m: &mut Module, id: u32, ty: Ty) {
    m.drop_glue.push(DropGlueEntry {
        glue: FuncId::new(id),
        ty,
    });
}
fn mixed() -> Module {
    let mut m = module(vec![
        drop_inst(Ty::Refine(TyId::new(0), PredId::new(4)), false),
        drop_inst(Ty::Unit, true),
        direct(7, 0),
    ]);
    m.types.push(Ty::U8);
    register(&mut m, 7, Ty::Struct(StructId::new(3)));
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let expected = super::super::validate_drop_sites(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_drop_sites_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, expected);
    let copy = out.clone();
    let bound = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (copy, o, bound)
}
fn error(function: &str, block: u32, reason: &str) -> ValidationError {
    ValidationError::NonCanonicalDrop {
        function: function.into(),
        block,
        reason: reason.into(),
    }
}
fn prior() -> ValidationError {
    error("already owned λ\0TAIL", 5, "prior full reason 尾\0TAIL")
}
fn type_reason(ty: &Ty, refined: bool) -> String {
    if refined {
        format!(
            "a drop of the refined type {ty}: a refinement has its base's representation, so the drop is spelled at the base"
        )
    } else {
        format!(
            "a drop of the trivially droppable type {ty}: a drop that does nothing is spelled by absence"
        )
    }
}
fn direct_reason(id: u32, what: &str) -> String {
    format!(
        "a direct {what} of registered drop glue @func.{id}: a destructor runs only through a drop (Drop / DropInvoke), so every destructor run is a site a verifier can find; take the glue's address for dynamic dispatch"
    )
}
fn seeded() -> State {
    State {
        errors: vec![prior()],
        ..State::default()
    }
}
fn empty(s: &State) -> bool {
    s.ty.capacity() == 0
        && s.reason.capacity() == 0
        && s.name.capacity() == 0
        && s.errors.capacity() == 0
}
