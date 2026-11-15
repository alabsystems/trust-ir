// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual independently authored source family for the complete entry control.
use super::*;
use clean_kernel::{Declaration, Name};
use trust_ir::ProofId;
use trust_ir::proof::{
    IslandEnvironment, ProofLineageId, SourceDefinitionRef, encode_island_declarations_v1,
};
fn domains() -> [Expr; 3] {
    [
        Expr::const_str("IRByteContextV1"),
        Expr::const_str("IRByteMemoryV1"),
        constant("Nat"),
    ]
}
fn function_type() -> Expr {
    domains()
        .into_iter()
        .rev()
        .fold(Expr::const_str("IRByteMemoryResultV1"), |body, domain| {
            Expr::pi(BinderInfo::Default, domain, body)
        })
}
fn lambda(body: Expr) -> Expr {
    domains().into_iter().rev().fold(body, |body, domain| {
        Expr::lam(BinderInfo::Default, domain, body)
    })
}
fn source_island(coinciding_constant: bool) -> IslandEnvironment {
    source_island_at(coinciding_constant, false)
}
fn source_island_at(coinciding_constant: bool, shifted: bool) -> IslandEnvironment {
    // This source is authored independently of module()/its target denotation.
    // It specifies the existing total operation, including access failures and
    // unchanged memory. The caller applies the separately defined source leaf.
    let read = if coinciding_constant {
        Expr::apps(
            Expr::const_str("IRByteMemoryResultV1.value"),
            [
                Expr::app(Expr::const_str("IRScalar.int_"), Expr::nat_lit(41)),
                Expr::bvar(1),
            ],
        )
    } else {
        Expr::apps(
            Expr::const_str("ir_byte_load_v1"),
            [
                Expr::bvar(2),
                Expr::app(Expr::const_str("IRTy.uint_"), Expr::nat_lit(64)),
                Expr::app(
                    Expr::const_str("IRScalar.ptr_"),
                    if shifted {
                        Expr::apps(
                            Expr::const_str("Nat.add"),
                            [Expr::bvar(0), Expr::nat_lit(8)],
                        )
                    } else {
                        Expr::bvar(0)
                    },
                ),
                Expr::nat_lit(8),
                Expr::const_str("Bool.false"),
                Expr::bvar(1),
            ],
        )
    };
    let definition = |name: &str, value| Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: function_type(),
        value: lambda(value),
        is_reducible: true,
    };
    IslandEnvironment::new(
        encode_island_declarations_v1(&[
            definition("Source.readWord", read),
            definition(
                "Source.forwardRead",
                Expr::apps(
                    Expr::const_str("Source.readWord"),
                    [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                ),
            ),
        ])
        .unwrap(),
    )
}

pub(super) fn license(module: &mut Module) {
    let island = source_island(false);
    let selectors = [(1, "Source.forwardRead"), (0, "Source.readWord")].map(|(n, name)| {
        (
            module.functions[n].id,
            SourceDefinitionRef {
                decl: name.into(),
                closure_digest: island.digest,
            },
        )
    });
    let rows = crate::certify_source_bound_readonly_call_family(
        module,
        ProofLineageId::new(10),
        ProofId::new(20),
        trust_ir::proof::ProofTransform::new(
            trust_ir::proof::ProofTransformStage::Frontend,
            "readonly-licensed-entry-control",
            "independent-source",
            "1",
        ),
        &island,
        &selectors,
    )
    .unwrap();
    module.proof_obligations.extend(rows.obligations);
    module.proof_certificates.extend(rows.certificates);
    for ordinal in 0..module.functions.len() {
        let id = module.functions[ordinal].id;
        let obligation = module
            .proof_obligations
            .iter()
            .find(|o| o.function == Some(id))
            .unwrap()
            .id;
        let body_digest = module.function_body_digest(id).unwrap();
        module.functions[ordinal].body_gate = Some(trust_ir::BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(trust_ir::GateEvidence {
                obligation,
                body_digest,
            }),
        });
    }
}
