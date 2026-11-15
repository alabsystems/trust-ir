// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn fixture() -> Module {
    let mut m = Module::new("spec reservation");
    m.spec_modules
        .push(SpecModule::new(CLEAN_ORIGIN_DISCLOSURE));
    m
}
pub(super) fn function(id: u32, body: bool) -> Function {
    let mut f = Function::new(
        FuncId::new(id),
        "irrelevant",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    if body {
        f.blocks.push(trust_ir::Block::new(BlockId::new(0)));
    }
    f
}
pub(super) fn rows(m: &mut Module, names: &[&str]) {
    m.spec_modules[0].invariants = names
        .iter()
        .map(|name| trust_ir::SpecInvariant::new(*name, "opaque"))
        .collect();
}
pub(super) fn offenders() -> Module {
    let mut m = fixture();
    let s = &mut m.spec_modules[0];
    s.vars.push(trust_ir::SpecVar::new("x", "unreadable"));
    s.actions.push("A".into());
    s.anchors.push(trust_ir::SpecAnchor {
        machine: "M".into(),
        action: "A".into(),
        rust_symbol: "f".into(),
        span: "raw".into(),
        project: None,
        function: None,
        projection_target: None,
    });
    s.waivers.push(trust_ir::SpecWaiver {
        machine: "M".into(),
        action: "A".into(),
        reason: "raw".into(),
    });
    s.proofs.push(trust_ir::SpecProof {
        machine: "M".into(),
        action: "A".into(),
        proof_name: "p".into(),
        kind: trust_ir::ProofKind::Kani,
    });
    s.enforcement = SpecEnforcementMode::Linked;
    s.origin = SpecOrigin::External("λ'\norigin".into());
    m
}
