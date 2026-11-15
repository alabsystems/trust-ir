// Copyright 2026 Andrew Yates | Apache-2.0
//! Independently authored ordinary memory-reading source, not TLA or a
//! constant-specialized return. The proof is equality of WHOLE effect functions.
use super::*;
use trust_ir::{CallingConv, Endianness, GateEvidence, Linkage, TargetInfo};
use trust_ir_build::certify_source_bound_readonly_call_family;

fn domains() -> [Expr; 3] {
    [
        Expr::const_str("IRByteContextV1"),
        Expr::const_str("IRByteMemoryV1"),
        nat(),
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
fn module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(
        "ordinary_readonly_source",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("darwinpcs".into()),
            struct_passing: Default::default(),
        },
    );
    let sig = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let mut f = mb.function("read_word", sig);
    f.set_calling_conv(CallingConv::C);
    f.set_linkage(Linkage::Internal);
    let block = f.create_block();
    let ptr = f.add_block_param(block, Ty::Ptr);
    f.switch_to_block(block);
    let word = f.load_aligned(Ty::U64, ptr, 8);
    f.ret(vec![word]);
    let leaf = f.build();
    let mut f = mb.function("forward_read", sig);
    f.set_calling_conv(CallingConv::C);
    let block = f.create_block();
    let ptr = f.add_block_param(block, Ty::Ptr);
    f.switch_to_block(block);
    let word = f.call(leaf, vec![ptr]);
    f.ret(vec![word]);
    f.build();
    mb.build().unwrap()
}
fn selectors(m: &Module, i: &IslandEnvironment) -> Vec<(FuncId, SourceDefinitionRef)> {
    [1, 0]
        .map(|n| {
            (
                m.functions[n].id,
                SourceDefinitionRef {
                    decl: ["Source.readWord", "Source.forwardRead"][n].into(),
                    closure_digest: i.digest,
                },
            )
        })
        .to_vec()
}
fn mint(
    m: &Module,
    i: &IslandEnvironment,
) -> Result<trust_ir_build::SourceBoundCallCertificates, String> {
    certify_source_bound_readonly_call_family(
        m,
        ProofLineageId::new(10),
        ProofId::new(20),
        transform(),
        i,
        &selectors(m, i),
    )
}
fn attach(
    m: &mut Module,
    rows: trust_ir_build::SourceBoundCallCertificates,
) -> ProofLineageManifest {
    let manifest = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        roots: rows.nodes.iter().map(|n| n.id).collect(),
        nodes: rows.nodes,
    };
    m.proof_obligations.extend(rows.obligations);
    m.proof_certificates.extend(rows.certificates);
    for ordinal in 0..m.functions.len() {
        let id = m.functions[ordinal].id;
        let obligation = m
            .proof_obligations
            .iter()
            .find(|o| o.function == Some(id))
            .unwrap()
            .id;
        let body_digest = m.function_body_digest(id).unwrap();
        m.functions[ordinal].body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(GateEvidence {
                obligation,
                body_digest,
            }),
        });
    }
    manifest
}
#[test]
fn universal_readonly_source_family_replays_and_licenses_actual_pointer_bodies() {
    let mut m = module();
    let rows = mint(&m, &source_island(false)).unwrap();
    let manifest = attach(&mut m, rows);
    let report = validate_module_with_config(
        &m,
        &ValidationConfig::pinned()
            .with_bound_certificates(true)
            .with_source_bound_certificates(true)
            .with_gate_evidence(true),
    );
    assert!(report.is_ok(), "{:?}", report.errors());
    let owner =
        trust_ir_build::source_readonly_calls::check_readonly_source_family(&report).unwrap();
    assert!(std::ptr::eq(owner.module(), &m));
    assert_eq!(
        owner.functions_in(&m),
        Ok((m.functions[1].id, m.functions[0].id))
    );
    assert!(owner.functions_in(&m.clone()).is_err());
    assert_eq!(
        owner.source(m.functions[0].id).unwrap().decl,
        "Source.readWord"
    );
    assert!(
        validate_module_for_codegen(&m).is_empty(),
        "{:?}",
        validate_module_for_codegen(&m)
    );
    assert_eq!(
        lineage_closed_with_validated_authority(&m, &manifest),
        Ok(())
    );
}
#[test]
fn universal_readonly_source_refuses_pointwise_coincidence_and_scalar_anchor() {
    let m = module();
    let wrong = source_island(true);
    assert!(
        mint(&m, &wrong).is_err(),
        "41 at one row is not a memory function theorem"
    );
    assert!(
        mint(&m, &source_island_at(false, true)).is_err(),
        "a source reading another address cannot receive the original body license"
    );
    let i = source_island(false);
    assert!(
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(10),
            ProofId::new(20),
            transform(),
            &i,
            &selectors(&m, &i)
        )
        .is_err(),
        "old scalar profile stays closed"
    );
}
#[test]
fn readonly_source_refuses_changed_width_alignment_target_and_hidden_effect() {
    let i = source_island(false);
    for mutation in 0..5 {
        let mut m = module();
        let caller_id = m.functions[1].id;
        match mutation {
            0 => {
                if let Inst::Load { ty, .. } = &mut m.functions[0].blocks[0].body[0].inst {
                    *ty = Ty::U32
                }
            }
            1 => {
                if let Inst::Load { align, .. } = &mut m.functions[0].blocks[0].body[0].inst {
                    *align = Some(1)
                }
            }
            2 => {
                if let Inst::Call { callee, .. } = &mut m.functions[1].blocks[0].body[0].inst {
                    *callee = caller_id
                }
            }
            3 => m.target_info.as_mut().unwrap().endianness = Endianness::Big,
            _ => {
                let last = m.functions[0].blocks[0].body.last().unwrap().clone();
                m.functions[0].blocks[0].body.push(last);
            }
        }
        assert!(mint(&m, &i).is_err(), "mutation{mutation}");
    }
}
#[test]
fn readonly_source_stale_proof_source_and_family_edges_do_not_license_mutations() {
    let mut m = module();
    let rows = mint(&m, &source_island(false)).unwrap();
    attach(&mut m, rows);
    let mut wrong_body = m.clone();
    if let Inst::Load { volatile, .. } = &mut wrong_body.functions[0].blocks[0].body[0].inst {
        *volatile = true
    };
    assert!(!validate_module_for_codegen(&wrong_body).is_empty());
    let mut wrong_source = m.clone();
    let certificate = wrong_source
        .proof_certificates
        .iter_mut()
        .find(|c| matches!(c.evidence, ProofEvidence::CleanCic { .. }))
        .unwrap();
    binding(certificate).source.as_mut().unwrap().decl = "Source.absent".into();
    assert!(!validate_module_for_codegen(&wrong_source).is_empty());
    let mut missing_leaf = m.clone();
    let leaf = missing_leaf.functions[0].id;
    let id = missing_leaf
        .proof_obligations
        .iter()
        .find(|o| o.function == Some(leaf))
        .unwrap()
        .id;
    missing_leaf
        .proof_certificates
        .retain(|c| c.obligation != id);
    assert!(!validate_module_for_codegen(&missing_leaf).is_empty());
}
