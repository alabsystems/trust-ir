// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! UNRUN data checks with cfg(test)-only replay-result fixtures, NOT replay evidence.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{ObligationKind, ProofCertificate, ProofDigest, ProofEvidence};
use trust_ir::value::FuncTyId;
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
            return Err("postcheck stop");
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
struct Input {
    module: Module,
    tv: Vec<TvRechecked>,
    islands: Vec<IslandTheoremRechecked>,
    rows: Vec<ProofObligation>,
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(601))
}
fn digest(n: u8) -> ProofDigest {
    ProofDigest::sha256([n; 32])
}
fn inherited(caller: u32, callee: u32, far: u32) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(caller),
        prover: "postcheck".into(),
        assurance: None,
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(callee),
            obligation: ProofId::new(far),
            external: None,
        },
    }
}
fn tv(id: u32, function: u32, callees: &[u32], decl: Option<&str>) -> TvRechecked {
    TvRechecked {
        obligation: ProofId::new(id),
        function: FuncId::new(function),
        callees: callees.iter().copied().map(FuncId::new).collect(),
        island: decl.map(|s| (digest(3), s.into())),
    }
}
fn theorem(
    id: u32,
    name: &str,
    island: u8,
    statement: u8,
    cited: &[&str],
) -> IslandTheoremRechecked {
    IslandTheoremRechecked {
        obligation: ProofId::new(id),
        theorem: name.into(),
        island: digest(island),
        statement: digest(statement),
        cited: cited.iter().map(|s| (*s).into()).collect(),
    }
}
fn row(id: u32, owner: Option<u32>, description: &str) -> ProofObligation {
    let mut r = ProofObligation::new(
        ProofId::new(id),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        description,
    );
    r.function = owner.map(FuncId::new);
    r
}
fn fixture() -> Input {
    let mut module = Module::new("private post-replay data");
    module.functions = [(3, "calleré🦀"), (7, "calleeé🦀"), (9, "third")]
        .into_iter()
        .map(|(id, name)| Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0)))
        .collect();
    module.proof_certificates = vec![
        inherited(10, 7, 11),
        inherited(10, 9, 12),
        inherited(11, 9, 12),
    ];
    Input {
        module,
        tv: vec![
            tv(10, 3, &[7, 9], Some("A")),
            tv(11, 7, &[9], Some("B")),
            tv(12, 9, &[], None),
        ],
        islands: vec![theorem(20, "claimé", 3, 5, &["A", "B"])],
        rows: vec![
            row(31, Some(3), "same"),
            row(30, Some(3), "same"),
            row(32, None, "other"),
        ],
    }
}
fn oracle(i: &Input, catalog: &ModuleFunctionCatalog<'_>) -> Vec<ValidationError> {
    let mut out = validate_tv_call_edge_binding(&i.module, catalog, &i.tv);
    out.extend(island_symbol_bridge_errors(&i.islands, &i.tv));
    out.extend(island_theorem_name_errors(&i.islands));
    let rows: Vec<_> = i.rows.iter().collect();
    out.extend(duplicate_obligation_content_errors(&rows, &|id| {
        catalog.unique(id).map(|f| f.name.clone())
    }));
    out
}
fn call<O: ExecutionObserver>(
    i: &Input,
    catalog: &ModuleFunctionCatalog<'_>,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    let rows: Vec<_> = i.rows.iter().collect();
    checks(&i.module, catalog, &i.tv, &i.islands, &rows, s, site())
}
fn run(i: &Input) -> (Observer, usize) {
    let catalog = ModuleFunctionCatalog::new(&i.module);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(i, &catalog, &mut s).unwrap();
    let end = calls.get();
    assert_eq!(out, oracle(i, &catalog));
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (o, end)
}
fn cycle_fixture() -> Input {
    let mut i = fixture();
    i.rows.clear();
    i.islands.clear();
    i.tv = vec![
        tv(10, 3, &[7, 9], None),
        tv(11, 7, &[9, 3], None),
        tv(12, 9, &[3], None),
    ];
    i.module.proof_certificates = vec![
        inherited(10, 7, 11),
        inherited(10, 9, 12),
        inherited(11, 9, 12),
        inherited(11, 3, 10),
        inherited(12, 3, 10),
    ];
    i
}
