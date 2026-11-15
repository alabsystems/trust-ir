// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN source controls, no execution claim.
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::GlobalId;
use trust_ir::{Block, FuncTyId, InstrNode};
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original global stop");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(123))
}
fn fixture() -> Module {
    let mut m = Module::new("global-addresses");
    let mut f = Function::new(
        FuncId::new(123),
        "global",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    for id in [0, 9, 0] {
        let mut b = Block::new(BlockId::new(id));
        for global in [0, 1, u32::MAX] {
            b.body.push(InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(global),
            }));
        }
        f.blocks.push(b);
    }
    m.functions = vec![f.clone(), f];
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_global_addresses_observed(m, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert_eq!(out, validate_global_addrs(m));
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
#[test]
fn every_stored_duplicate_unreachable_row_keeps_original_order() {
    let m = fixture();
    let (out, _) = run(&m);
    assert_eq!(out.len(), 18);
    assert_eq!(
        out[0],
        ValidationError::GlobalNotFound {
            block: 0,
            global_id: 0
        }
    );
    assert_eq!(
        out[8],
        ValidationError::GlobalNotFound {
            block: 0,
            global_id: u32::MAX
        }
    );
}
#[test]
fn global_table_length_is_the_only_original_reference_bound() {
    let mut m = fixture();
    m.globals.push(trust_ir::Global {
        name: "arbitrary".into(),
        ty: Ty::Error,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    let (out, _) = run(&m);
    assert_eq!(out.len(), 12);
    assert!(out.iter().all(|e| matches!(
        e,
        ValidationError::GlobalNotFound {
            global_id: 1 | u32::MAX,
            ..
        }
    )));
}
#[test]
fn no_globaladdr_is_exempted_by_function_linkage_or_inactive_entry() {
    let mut m = fixture();
    m.functions[0].linkage = Linkage::External;
    m.functions[0].entry = BlockId::new(999);
    assert_eq!(run(&m).0.len(), 18);
    m.functions[0].blocks.clear();
    assert_eq!(run(&m).0.len(), 9);
    m.functions.clear();
    assert!(run(&m).0.is_empty());
}
#[test]
fn unrelated_large_instruction_payload_is_not_walked_by_this_specific_rule() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Const {
        ty: Ty::Tuple(vec![Ty::U8; 10_000]),
        value: Constant::Aggregate(vec![Constant::Int(3); 10_000]),
    })];
    let (out, o) = run(&m);
    assert_eq!(out.len(), 15);
    assert!(o.work < 10_000);
}
