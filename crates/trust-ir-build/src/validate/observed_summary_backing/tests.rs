// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN against the exact original citation-policy block.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, ImportId, ProofId};
use trust_ir::{ExternRef, ModuleImport, ProofDigest};
mod oracle;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original backing");
        };
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("work");
        };
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        };
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(157))
}
fn fixture() -> (Module, Function, FunctionSummary) {
    let mut m = Module::new("citation");
    m.imports
        .push(ModuleImport::new("far", ProofDigest::sha256([3; 32])));
    let f = Function::new(
        FuncId::new(u32::MAX),
        "function",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut summary = FunctionSummary::new();
    summary.proved = true;
    summary.backed_by =
        Some(ExternRef::new(ImportId::new(0), "symbolλ'\n").relying_on(ProofId::new(u32::MAX)));
    (m, f, summary)
}
fn run(
    m: &Module,
    f: &Function,
    summary: &FunctionSummary,
    policy: ImportPolicy<'_>,
) -> ((Vec<ValidationError>, SummaryCitation), Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out =
        validate_function_summary_import_backing_observed(m, f, summary, policy, &mut s, site())
            .unwrap();
    assert_eq!(out, oracle::ordinary(m, f, summary, policy));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
