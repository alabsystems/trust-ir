// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! UNRUN data comparison contracts; supplied digests are not replay evidence.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{IslandEnvironment, ObligationKind};
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
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("binding stop");
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
    ExecutionSite::Entry(FuncId::new(630))
}
fn digest(n: u8) -> ProofDigest {
    ProofDigest::sha256([n; 32])
}
struct Input {
    module: Module,
    row: ProofObligation,
    binding: CertificateBinding,
    env: Option<ProofDigest>,
    statement: Option<ProofDigest>,
    callees: Vec<String>,
}
fn fixture() -> Input {
    let mut module = Module::new("binding");
    module.imports = vec![trust_ir::ModuleImport::new("dep", digest(3))];
    let row = ProofObligation::new(
        ProofId::new(7),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "data",
    );
    let mut binding = CertificateBinding::new(digest(1), digest(2));
    binding.origin_module = Some(digest(3));
    binding.callees = vec!["a".into(), "é🦀'\"\\\n\0\u{1248}".into()];
    let callees = binding.callees.clone();
    Input {
        module,
        row,
        binding,
        env: Some(digest(1)),
        statement: Some(digest(2)),
        callees,
    }
}
fn bad() -> Input {
    let mut i = fixture();
    i.env = None;
    i.statement = Some(digest(9));
    i.module.imports.clear();
    i.callees = vec!["different\u{1248}".into()];
    i
}
fn oracle(i: &Input) -> Vec<ValidationError> {
    certificate_binding_errors(
        &i.module,
        &i.row,
        &i.binding,
        i.env,
        i.statement,
        &i.callees,
    )
}
fn call<O: ExecutionObserver>(
    i: &Input,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    binding_errors(
        &i.module,
        &i.row,
        &i.binding,
        i.env,
        i.statement,
        &i.callees,
        s,
        site(),
    )
}
fn run(i: &Input) -> (Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(i, &mut s).unwrap();
    let end = calls.get();
    assert_eq!(out, oracle(i));
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (o, end)
}
