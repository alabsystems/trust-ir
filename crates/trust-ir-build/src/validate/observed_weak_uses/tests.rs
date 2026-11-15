// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; entire actual ordinary weak-use rule is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::{PanicLocation, PanicSite, SwitchCase};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::FuncTyId;
use trust_ir::{AssertKind, Block, InstrNode};
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
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original weak-use stop");
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
    ExecutionSite::Entry(FuncId::new(4011))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn weak(id: u32, name: &str, sig: u32) -> Function {
    let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(sig), BlockId::new(0));
    f.linkage = Linkage::ExternalWeak;
    f
}
fn symbol(name: &str) -> Constant {
    Constant::SymbolAddr {
        symbol: name.into(),
        addend: 0,
    }
}
fn definition(id: u32, value: Constant) -> InstrNode {
    InstrNode::new(Inst::Const { ty: Ty::Ptr, value }).with_result(v(id))
}
fn call(variant: u32, value: u32, sig: u32, conv: CallingConv) -> InstrNode {
    InstrNode::new(match variant {
        0 => Inst::CallIndirect {
            callee: v(value),
            sig: FuncTyId::new(sig),
            args: vec![],
            calling_conv: conv,
        },
        1 => Inst::CallIndirectCannotUnwind {
            callee: v(value),
            sig: FuncTyId::new(sig),
            args: vec![],
            calling_conv: conv,
        },
        _ => Inst::InvokeIndirect {
            callee: v(value),
            sig: FuncTyId::new(sig),
            args: vec![],
            calling_conv: conv,
            normal_dest: BlockId::new(9),
            normal_args: vec![],
            unwind_dest: BlockId::new(10),
        },
    })
}
fn switch(values: Vec<Constant>) -> InstrNode {
    InstrNode::new(Inst::Switch {
        value: v(1),
        default: BlockId::new(8),
        default_args: vec![],
        cases: values
            .into_iter()
            .map(|value| SwitchCase {
                value,
                target: BlockId::new(8),
                args: vec![],
            })
            .collect(),
        exhaustive_enum_unreachable: false,
    })
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.func_types = vec![
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(vec![Ty::Bool], vec![Ty::U64], false),
    ];
    let mut f = Function::new(
        FuncId::new(4011),
        "caller",
        FuncTyId::new(0),
        BlockId::new(7),
    );
    let mut b = Block::new(f.entry);
    b.body = vec![
        definition(1, symbol("weak")),
        InstrNode::new(Inst::Copy {
            ty: Ty::Ptr,
            operand: v(1),
        })
        .with_result(v(2)),
        call(0, 2, 0, CallingConv::Rust),
        InstrNode::new(Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        }),
        switch(vec![Constant::Aggregate(vec![
            Constant::FnDef(FuncId::new(9)),
            symbol("weak"),
        ])]),
    ];
    f.blocks.push(b);
    m.functions = vec![f, weak(9, "weak", 1)];
    m
}
fn original(m: &Module) -> Vec<ValidationError> {
    super::super::validate_weak_declaration_uses(m, &ModuleFunctionCatalog::new(m))
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let expected = original(m);
    let catalog = ModuleFunctionCatalog::new(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_weak_declaration_uses_observed(&catalog, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, end)
}
fn empty(s: &State<'_>) {
    assert!(s.current.is_none());
    assert_eq!(
        s.frames.capacity()
            + s.definitions.capacity()
            + s.location.capacity()
            + s.here.capacity()
            + s.name.capacity()
            + s.symbol.capacity()
            + s.detail.capacity()
            + s.declared.capacity()
            + s.actual.capacity()
            + s.render.capacity()
            + s.errors.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
