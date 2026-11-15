// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independently authored source declarations versus real caller/callee IR.
//! No source body is recovered from a target denotation or certificate.

use trust_ir::proof::{
    CertificateBinding, IslandEnvironment, KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1,
    KERNEL_ANCHOR_CLEAN_BACKEND_TV, ProofDigest, ProofEvidence, ProofLineageId,
    ProofLineageManifest, ProofTransform, ProofTransformStage, SourceDefinitionRef,
    clean_cic_lineage_digest_v8, encode_clean_expr_v1, encode_island_declarations_v1,
    module_symbol_resolver,
};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir::{BodyGate, FuncId, Inst, Module, Producer};
use trust_ir_build::clean_kernel::env::Declaration;
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Name};
use trust_ir_build::{
    ModuleBuilder, ValidationConfig, certify_identity_lineage_rung_island_bound,
    certify_source_bound_call_family, lineage_closed_with_validated_authority, validate_module,
    validate_module_for_codegen, validate_module_with_config,
};

fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn lam(body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat(), body)
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [a, b])
}
fn wrap(e: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.mod"), [e, Expr::nat_lit(256)])
}
fn app(name: &str, arg: Expr) -> Expr {
    Expr::app(Expr::const_str(name), arg)
}
fn definition(name: &str, value: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::arrow(nat(), nat()),
        value,
        is_reducible: true,
    }
}
fn island(changed_leaf: bool) -> IslandEnvironment {
    // Source module written independently: inc x = (x+1)%256,
    // caller x = (inc x+3)%256, root x = caller(inc x).
    let delta = if changed_leaf { 2 } else { 1 };
    IslandEnvironment::new(
        encode_island_declarations_v1(&[
            definition(
                "Source.inc",
                lam(wrap(add(Expr::bvar(0), Expr::nat_lit(delta)))),
            ),
            definition(
                "Source.other",
                lam(wrap(add(Expr::bvar(0), Expr::nat_lit(2)))),
            ),
            definition(
                "Source.caller",
                lam(wrap(add(
                    app("Source.inc", Expr::bvar(0)),
                    Expr::nat_lit(3),
                ))),
            ),
            definition(
                "Source.root",
                lam(app("Source.caller", app("Source.inc", Expr::bvar(0)))),
            ),
        ])
        .unwrap(),
    )
}
fn source(name: &str) -> SourceDefinitionRef {
    SourceDefinitionRef {
        decl: name.into(),
        closure_digest: ProofDigest::sha256([0x92; 32]),
    }
}
fn transform() -> ProofTransform {
    ProofTransform::new(
        ProofTransformStage::Frontend,
        "source-bound-call-composition",
        "independent-source",
        "1",
    )
}
fn module() -> Module {
    let mut mb = ModuleBuilder::new("source_bound_calls");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
    let mut leaf = |name: &str, delta: i128| {
        let mut f = mb.function(name, sig);
        let e = f.create_block();
        let x = f.add_block_param(e, Ty::U8);
        f.switch_to_block(e);
        let k = f.iconst(Ty::U8, delta);
        let y = f.add(Ty::U8, x, k);
        f.ret(vec![y]);
        f.build()
    };
    let inc = leaf("inc", 1);
    let _ = leaf("other", 2);
    let caller = {
        let mut f = mb.function("caller", sig);
        let e = f.create_block();
        let x = f.add_block_param(e, Ty::U8);
        f.switch_to_block(e);
        let a = f.call(inc, vec![x]);
        let k = f.iconst(Ty::U8, 3);
        let y = f.add(Ty::U8, a, k);
        f.ret(vec![y]);
        f.build()
    };
    let mut f = mb.function("root", sig);
    let e = f.create_block();
    let x = f.add_block_param(e, Ty::U8);
    f.switch_to_block(e);
    let a = f.call(inc, vec![x]);
    let y = f.call(caller, vec![a]);
    f.ret(vec![y]);
    f.build();
    let mut m = mb.build().unwrap();
    for f in &mut m.functions {
        f.body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: None,
        });
    }
    m
}
fn sources(m: &Module) -> Vec<(FuncId, SourceDefinitionRef)> {
    // Deliberately reverse topological/module/symbol order. No positional
    // assumption can accidentally supply callee authority.
    [3, 2, 1, 0]
        .iter()
        .map(|i| {
            (
                m.functions[*i].id,
                source(["Source.inc", "Source.other", "Source.caller", "Source.root"][*i]),
            )
        })
        .collect()
}
fn mint(m: &Module, i: &IslandEnvironment) -> trust_ir_build::SourceBoundCallCertificates {
    certify_source_bound_call_family(
        m,
        ProofLineageId::new(10),
        ProofId::new(20),
        transform(),
        i,
        &sources(m),
    )
    .unwrap()
}
fn certified() -> (Module, ProofLineageManifest) {
    let mut m = module();
    let rows = mint(&m, &island(false));
    let manifest = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        roots: rows.nodes.iter().map(|n| n.id).collect(),
        nodes: rows.nodes,
    };
    m.proof_obligations.extend(rows.obligations);
    m.proof_certificates.extend(rows.certificates);
    (m, manifest)
}
fn binding(c: &mut trust_ir::proof::ProofCertificate) -> &mut CertificateBinding {
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(d),
        ..
    } = &mut c.evidence
    else {
        panic!("kernel fixture")
    };
    d.binding.as_deref_mut().unwrap()
}
fn rekey(m: &mut Module) {
    let resolve = module_symbol_resolver(m);
    let changes: Vec<_> = m
        .proof_certificates
        .iter()
        .enumerate()
        .filter_map(|(i, c)| {
            let ProofEvidence::CleanCic {
                kernel_recheck: Some(d),
                ..
            } = &c.evidence
            else {
                return None;
            };
            let o = m
                .proof_obligations
                .iter()
                .find(|o| o.id == c.obligation)
                .unwrap();
            Some((
                i,
                clean_cic_lineage_digest_v8(o, &resolve, d.binding.as_deref()).unwrap(),
            ))
        })
        .collect();
    drop(resolve);
    for (i, l) in changes {
        let ProofEvidence::CleanCic { lineage, .. } = &mut m.proof_certificates[i].evidence else {
            unreachable!()
        };
        *lineage = l;
    }
}
fn refused(m: &Module, text: &str) {
    let e = validate_module(m);
    assert!(!e.is_empty(), "tamper must refuse");
    assert!(format!("{e:?}").contains(text), "wanted {text}, got {e:?}");
}
#[test]
fn complete_independent_source_family_replays_in_ordinary_module_and_lineage_validation() {
    let (m, lineage) = certified();
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert!(
        validate_module_for_codegen(&m).is_empty(),
        "{:?}",
        validate_module_for_codegen(&m)
    );
    let r = validate_module_with_config(
        &m,
        &ValidationConfig::pinned()
            .with_source_bound_certificates(true)
            .with_bound_certificates(true),
    );
    assert!(r.is_ok(), "{:?}", r.errors());
    assert_eq!(
        lineage_closed_with_validated_authority(&m, &lineage),
        Ok(())
    );
}
#[test]
fn wrong_independent_callee_source_and_wrong_actual_body_refuse_at_mint_time() {
    let m = module();
    let e = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &island(true),
        &sources(&m),
    )
    .unwrap_err();
    assert!(e.contains("kernel refusal"), "{e}");
    let mut m = module();
    let Inst::BinOp { op, .. } = &mut m.functions[0].blocks[0].body[1].inst else {
        panic!()
    };
    *op = trust_ir::BinOp::Sub;
    assert!(
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &island(false),
            &sources(&m)
        )
        .is_err()
    );
}
#[test]
fn old_island_bound_no_callee_contract_still_refuses_caller() {
    let m = module();
    let e = certify_identity_lineage_rung_island_bound(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        m.functions[2].id,
        &island(false),
        source("Source.caller"),
    )
    .unwrap_err();
    assert!(e.contains("slice 2"));
}
#[test]
fn missing_or_duplicate_source_binding_and_foreign_body_refuse() {
    let m = module();
    let mut s = sources(&m);
    s.pop();
    assert!(
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &island(false),
            &s
        )
        .unwrap_err()
        .contains("misses actual callee")
    );
    let mut s = sources(&m);
    s[0].1 = s[1].1.clone();
    assert!(
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &island(false),
            &s
        )
        .unwrap_err()
        .contains("duplicate")
    );
    let mut m = module();
    m.functions[0].blocks.clear();
    assert!(
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &island(false),
            &sources(&m)
        )
        .unwrap_err()
        .contains("defined bodies")
    );
}
#[test]
fn changed_actual_callee_body_cannot_keep_a_previously_valid_family() {
    let (mut m, _) = certified();
    let Inst::BinOp { op, .. } = &mut m.functions[0].blocks[0].body[1].inst else {
        panic!()
    };
    *op = trust_ir::BinOp::Sub;
    refused(&m, "source equation kernel refusal");
}
#[test]
fn retargeting_actual_call_and_inherited_edge_does_not_retarget_source() {
    let (mut m, _) = certified();
    let other = m.functions[1].id;
    let Inst::Call { callee, .. } = &mut m.functions[2].blocks[0].body[0].inst else {
        panic!()
    };
    *callee = other;
    let other_obligation = m
        .proof_obligations
        .iter()
        .find(|o| o.function == Some(other))
        .unwrap()
        .id;
    for c in &mut m.proof_certificates {
        if let ProofEvidence::InheritedFromCallee {
            callee, obligation, ..
        } = &mut c.evidence
            && c.obligation == ProofId::new(21)
        {
            *callee = other;
            *obligation = other_obligation;
        }
    }
    refused(&m, "source equation kernel refusal");
}
#[test]
fn missing_callee_certificate_is_not_opaque_authority() {
    let (mut m, _) = certified();
    let inc = m.functions[0].id;
    let id = m
        .proof_obligations
        .iter()
        .find(|o| o.function == Some(inc))
        .unwrap()
        .id;
    m.proof_obligations.retain(|o| o.id != id);
    m.proof_certificates.retain(|c| c.obligation != id);
    refused(&m, "misses actual callee");
}
#[test]
fn source_none_and_island_none_are_refused_even_after_rekeying() {
    for field in ["source", "environment"] {
        let (mut m, _) = certified();
        let b = binding(&mut m.proof_certificates[0]);
        if field == "source" {
            b.source = None
        } else {
            b.environment = None
        }
        rekey(&mut m);
        refused(
            &m,
            if field == "source" {
                "every source definition"
            } else {
                "checked island"
            },
        );
    }
}
#[test]
fn inconsistent_environment_and_wrong_source_decl_refuse_after_rekeying() {
    let (mut m, _) = certified();
    binding(&mut m.proof_certificates[0]).environment = Some(island(true));
    rekey(&mut m);
    refused(&m, "environments differ");
    let (mut m, _) = certified();
    binding(&mut m.proof_certificates[0]).source = Some(source("Nat.add"));
    rekey(&mut m);
    refused(&m, "not in this checked island");
}
#[test]
fn caller_context_is_the_exact_source_constant_not_a_free_comparand() {
    let (mut m, _) = certified();
    let ProofEvidence::CleanCic { context, .. } = &mut m.proof_certificates[0].evidence else {
        panic!()
    };
    *context = encode_clean_expr_v1(&lam(Expr::bvar(0))).unwrap();
    rekey(&mut m);
    refused(&m, "exact source constant");
}
#[test]
fn wrong_statement_environment_callee_binding_or_module_is_not_authority() {
    for field in ["statement", "digest", "callees", "module"] {
        let (mut m, _) = certified();
        if field == "module" {
            let ProofEvidence::CleanCic {
                kernel_recheck: Some(d),
                ..
            } = &mut m.proof_certificates[0].evidence
            else {
                panic!()
            };
            d.module = "CleanCompiler.BackendTV".into();
        } else {
            let b = binding(&mut m.proof_certificates[0]);
            match field {
                "statement" => b.statement_digest = ProofDigest::sha256([9; 32]),
                "digest" => b.environment_digest = ProofDigest::sha256([9; 32]),
                _ => b.callees = vec!["wrong".into()],
            }
        }
        rekey(&mut m);
        refused(
            &m,
            if field == "module" {
                "canonical module"
            } else {
                "binding mismatch"
            },
        );
    }
}
#[test]
fn wrong_arity_and_recursion_refuse_without_new_callee_allowances() {
    let mut m = module();
    let Inst::Call { args, .. } = &mut m.functions[2].blocks[0].body[0].inst else {
        panic!()
    };
    args.clear();
    assert!(
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &island(false),
            &sources(&m)
        )
        .unwrap_err()
        .contains("argument")
    );
    let mut m = module();
    let root = m.functions[3].id;
    let Inst::Call { callee, .. } = &mut m.functions[2].blocks[0].body[0].inst else {
        panic!()
    };
    *callee = root;
    assert!(
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &island(false),
            &sources(&m)
        )
        .unwrap_err()
        .contains("recursive")
    );
}
#[test]
fn no_added_axiom_policy_and_old_anchor_cannot_borrow_new_semantics() {
    let (mut m, _) = certified();
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(d),
        ..
    } = &mut m.proof_certificates[0].evidence
    else {
        panic!()
    };
    d.allowed_axioms.push("extra".into());
    rekey(&mut m);
    refused(&m, "no added axioms");
    let (mut m, _) = certified();
    for c in &mut m.proof_certificates {
        if let ProofEvidence::CleanCic {
            kernel_recheck: Some(d),
            ..
        } = &mut c.evidence
        {
            d.anchor = KERNEL_ANCHOR_CLEAN_BACKEND_TV.into();
            d.module = "CleanCompiler.BackendTV".into();
        }
    }
    rekey(&mut m);
    assert!(!validate_module(&m).is_empty());
}
#[test]
fn new_anchor_is_distinct_and_ids_do_not_select_foreign_function_authority() {
    assert_ne!(
        KERNEL_ANCHOR_CLEAN_BACKEND_TV,
        KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1
    );
    let mut m = module();
    let mut s = sources(&m);
    s[0].0 = FuncId::new(999);
    assert!(
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &island(false),
            &s
        )
        .is_err()
    );
    m.functions[0].id = m.functions[1].id;
    assert!(
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &island(false),
            &sources(&m)
        )
        .is_err()
    );
}
#[cfg(feature = "serde")]
#[test]
fn existing_json_and_messagepack_transport_preserve_and_replay_new_anchor_bindings() {
    let (m, _) = certified();
    let json = serde_json::to_vec(&m).unwrap();
    let round: Module = serde_json::from_slice(&json).unwrap();
    assert!(validate_module(&round).is_empty());
    let msg = rmp_serde::to_vec(&m).unwrap();
    let round: Module = rmp_serde::from_slice(&msg).unwrap();
    assert!(validate_module(&round).is_empty());
}

#[test]
fn caller_budget_and_stop_are_not_reset_by_the_family_producer() {
    use trust_ir_build::clean_kernel::tc;
    let m = module();
    let i = island(false);
    let s = sources(&m);
    // Warm trusted prelude before installing a caller-owned ambient bound.
    assert_eq!(tc::declaration_budget_limit(), 0);
    let _ = mint(&m, &i);
    assert_eq!(
        tc::declaration_budget_limit(),
        0,
        "successful owned scope must retire"
    );
    tc::set_declaration_budget(1);
    let result = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &i,
        &s,
    );
    let exhausted = tc::declaration_budget_exhausted();
    tc::clear_declaration_budget();
    assert!(result.is_err());
    assert!(exhausted);
    let result = tc::run_until(Some(std::time::Instant::now()), || {
        certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &i,
            &s,
        )
    });
    assert!(
        result.is_none(),
        "expired caller deadline must expose no producer result"
    );
    assert_eq!(
        tc::declaration_budget_limit(),
        0,
        "stopped owned scope must retire"
    );
}
#[test]
fn ordinary_module_replay_requires_existing_inheritance_edges_too() {
    let (mut m, _) = certified();
    m.proof_certificates
        .retain(|c| !matches!(c.evidence, ProofEvidence::InheritedFromCallee { .. }));
    refused(&m, "Callee");
}
#[test]
fn actual_source_definition_signature_is_checked_not_selected_by_the_producer() {
    let m = module();
    let arity_two = Declaration::Definition {
        name: Name::from_string("Source.wrong"),
        level_params: vec![],
        type_: Expr::arrow(nat(), Expr::arrow(nat(), nat())),
        value: lam(lam(Expr::bvar(0))),
        is_reducible: true,
    };
    let i = IslandEnvironment::new(encode_island_declarations_v1(&[arity_two]).unwrap());
    let e = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &i,
        &[(m.functions[0].id, source("Source.wrong"))],
    )
    .unwrap_err();
    assert!(e.contains("source signature mismatch"), "{e}");
}
#[test]
fn environment_changes_change_semantic_roots_even_when_constant_names_do_not() {
    let m = module();
    let a = mint(&m, &island(false));
    let mut changed = module();
    let Inst::Const { value, .. } = &mut changed.functions[0].blocks[0].body[0].inst else {
        panic!()
    };
    *value = trust_ir::Constant::Int(2);
    let b = mint(&changed, &island(true));
    for (old, new) in a.nodes.iter().zip(&b.nodes) {
        assert_ne!(
            old.source_module, new.source_module,
            "same source name in a different environment is not the same semantic root"
        );
        assert_ne!(old.target_module, new.target_module);
    }
}
#[test]
fn copying_target_root_over_source_root_is_not_a_lineage_binding() {
    let (m, mut manifest) = certified();
    assert_ne!(
        manifest.nodes[0].source_module,
        manifest.nodes[0].target_module
    );
    manifest.nodes[0].source_module = manifest.nodes[0].target_module;
    assert!(lineage_closed_with_validated_authority(&m, &manifest).is_err());
}
#[cfg(feature = "binary")]
#[test]
fn existing_binary_transport_preserves_and_replays_the_complete_family() {
    let (m, _) = certified();
    let bytes = trust_ir::binary::serialize_module(&m).unwrap();
    let round = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert_eq!(round.proof_certificates, m.proof_certificates);
    assert!(validate_module(&round).is_empty());
}

#[test]
fn a_real_trusted_arith_proof_is_refused_by_the_shared_rooted_audit() {
    use trust_ir_build::clean_kernel::{ExprKind, Level};
    let (mut m, _) = certified();
    let ProofEvidence::CleanCic { term, context, .. } = &mut m.proof_certificates[0].evidence
    else {
        panic!()
    };
    let original = trust_ir::proof::decode_clean_expr_v1(term).unwrap();
    let ExprKind::App(refl_ty, target) = original.kind() else {
        panic!()
    };
    let ExprKind::App(_, ty) = refl_ty.kind() else {
        panic!()
    };
    let source = trust_ir::proof::decode_clean_expr_v1(context).unwrap();
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty.as_ref().clone(), target.as_ref().clone(), source],
    );
    let forged = Expr::app(
        Expr::const_(Name::from_string("trustedArith"), vec![Level::zero()]),
        goal,
    );
    *term = encode_clean_expr_v1(&forged).unwrap();
    rekey(&mut m);
    refused(&m, "rooted certification audit");
}
#[test]
fn discharged_callee_does_not_become_source_bound_kernel_authority() {
    let (mut m, _) = certified();
    let inc = m.functions[0].id;
    m.proof_obligations
        .iter_mut()
        .find(|o| o.function == Some(inc))
        .unwrap()
        .status = trust_ir::proof::ProofStatus::Discharged;
    rekey(&mut m);
    refused(&m, "misses actual callee");
}
#[test]
fn aggregate_admission_does_not_reset_for_large_source_call_input() {
    let mut m = module();
    m.name = "x".repeat(trust_ir::proof::CLEAN_EXPR_V1_MAX_NODES + 1);
    let error = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &island(false),
        &sources(&m),
    )
    .unwrap_err();
    assert!(error.contains("bounded input admission"), "{error}");
}

#[test]
fn source_resolution_preserves_actual_island_name_components() {
    // `Source` + string component "1" differs from the numeric component 1.
    // The binding's display selector resolves to the genuine decoded Name;
    // it is never reparsed into the other constant.
    let mut m = module();
    m.functions.truncate(1);
    let mut d = definition("unused", lam(wrap(add(Expr::bvar(0), Expr::nat_lit(1)))));
    let Declaration::Definition { name, .. } = &mut d else {
        panic!()
    };
    *name = Name::from_string("Source").str("1");
    let i = IslandEnvironment::new(encode_island_declarations_v1(&[d]).unwrap());
    let rows = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &i,
        &[(m.functions[0].id, source("Source.1"))],
    )
    .unwrap();
    m.proof_obligations.extend(rows.obligations);
    m.proof_certificates.extend(rows.certificates);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let ProofEvidence::CleanCic { context, .. } = &mut m.proof_certificates[0].evidence else {
        panic!()
    };
    *context = encode_clean_expr_v1(&Expr::const_(Name::from_string("Source.1"), vec![])).unwrap();
    rekey(&mut m);
    refused(&m, "exact source constant");
}
#[test]
fn huge_or_deep_unknown_source_selector_is_not_parsed_into_a_kernel_name() {
    let m = module();
    let i = island(false);
    for decl in [
        "x.".repeat(10_000),
        "x".repeat(trust_ir::proof::CLEAN_EXPR_V1_MAX_NODES + 1),
    ] {
        let mut s = sources(&m);
        s[0].1.decl = decl;
        let e = certify_source_bound_call_family(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            transform(),
            &i,
            &s,
        )
        .unwrap_err();
        assert!(
            e.contains("not in this checked island") || e.contains("allowance exhausted"),
            "{e}"
        );
    }
}

#[test]
fn existing_island_symbol_bridge_consumes_the_new_family_and_refuses_an_unbound_definition() {
    use trust_ir_build::clean_kernel::Level;
    let mut declarations =
        trust_ir::proof::decode_island_declarations_v1(&island(false).declarations).unwrap();
    for (name, source_name, result) in [
        ("Source.caller_zero", "Source.caller", 4),
        ("Source.other_zero", "Source.other", 2),
    ] {
        let proposition = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [
                nat(),
                app(source_name, Expr::nat_lit(0)),
                Expr::nat_lit(result),
            ],
        );
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [nat(), Expr::nat_lit(result)],
        );
        declarations.push(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: proposition,
            value: proof,
        });
    }
    let island = IslandEnvironment::new(encode_island_declarations_v1(&declarations).unwrap());
    let mut m = module();
    let rows = mint(&m, &island);
    m.proof_obligations.extend(rows.obligations);
    m.proof_certificates.extend(rows.certificates);
    for (id, name, formula) in [
        (100, "Source.caller_zero", "(= (Source.caller 0) 4)"),
        (101, "Source.other_zero", "(= (Source.other 0) 2)"),
    ] {
        let (o, c) = trust_ir_build::certify_island_theorem(
            ProofId::new(id),
            name,
            trust_ir::proof::ProofFormula::smtlib2(formula, "Bool"),
            &island,
        )
        .unwrap();
        m.proof_obligations.push(o);
        m.proof_certificates.push(c);
    }
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let other = m.functions[1].id;
    let id = m
        .proof_obligations
        .iter()
        .find(|o| o.function == Some(other))
        .unwrap()
        .id;
    m.proof_obligations.retain(|o| o.id != id);
    m.proof_certificates.retain(|c| c.obligation != id);
    refused(&m, "theorem cites @Source.other");
}

#[test]
fn ambiguous_source_display_is_refused_by_the_checked_island_owner() {
    let mut m = module();
    m.functions.truncate(1);
    let numeric = definition("Source.1", lam(wrap(add(Expr::bvar(0), Expr::nat_lit(1)))));
    let mut string = definition("unused", lam(wrap(add(Expr::bvar(0), Expr::nat_lit(2)))));
    let Declaration::Definition { name, .. } = &mut string else {
        panic!()
    };
    *name = Name::from_string("Source").str("1");
    let i = IslandEnvironment::new(encode_island_declarations_v1(&[numeric, string]).unwrap());
    let e = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &i,
        &[(m.functions[0].id, source("Source.1"))],
    )
    .unwrap_err();
    assert!(e.contains("island redeclares Source.1"), "{e}");
}
#[test]
fn exact_island_identity_disambiguates_unused_auxiliary_name_components() {
    let m = module();
    let mut a =
        trust_ir::proof::decode_island_declarations_v1(&island(false).declarations).unwrap();
    let aux = Declaration::Definition {
        name: Name::from_string("Aux").num(1),
        level_params: vec![],
        type_: nat(),
        value: Expr::nat_lit(7),
        is_reducible: true,
    };
    a.push(aux);
    let i = IslandEnvironment::new(encode_island_declarations_v1(&a).unwrap());
    let Declaration::Definition { name, .. } = a.last_mut().unwrap() else {
        panic!()
    };
    *name = Name::from_string("Aux").str("1");
    let j = IslandEnvironment::new(encode_island_declarations_v1(&a).unwrap());
    let x = mint(&m, &i);
    let y = mint(&m, &j);
    let env_digest = |p: &trust_ir_build::SourceBoundCallCertificates| {
        p.certificates[0]
            .evidence
            .clean_cic_kernel_recheck()
            .unwrap()
            .binding
            .as_ref()
            .unwrap()
            .environment_digest
    };
    assert_eq!(
        env_digest(&x),
        env_digest(&y),
        "control: legacy environment digest displays auxiliary declaration names"
    );
    assert_ne!(i.digest, j.digest);
    assert_ne!(x.nodes[0].source_module, y.nodes[0].source_module);
    assert_ne!(x.nodes[0].target_module, y.nodes[0].target_module);
}
#[test]
fn all_kernel_checkers_share_one_finite_family_pot_and_do_not_replace_a_larger_caller() {
    use trust_ir_build::clean_kernel::tc;
    let m = module();
    let i = island(false);
    let s = sources(&m);
    let cap = trust_ir::proof::CLEAN_EXPR_V1_MAX_NODES as u64;
    tc::set_declaration_budget(cap);
    let result = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &i,
        &s,
    );
    let used = tc::declaration_budget_used();
    let remaining = tc::declaration_budget_remaining();
    let limit = tc::declaration_budget_limit();
    tc::clear_declaration_budget();
    result.unwrap();
    assert_eq!(limit, cap);
    assert!(used > 0 && remaining > 0 && used + remaining == cap);
    eprintln!(
        "complete four-member family kernel ticks (equations + legacy audits + source island): {used}/{cap}"
    );
    // Same checked island/setup, one genuine leaf equation. Choose a caller
    // allowance between this measured cost and the complete family's cost.
    // Replacing/refilling the pot before member checks could make this full
    // family pass; retaining the original pot must refuse on exhaustion.
    tc::set_declaration_budget(cap);
    let leaf = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &i,
        &[(m.functions[0].id, source("Source.inc"))],
    );
    let leaf_used = tc::declaration_budget_used();
    tc::clear_declaration_budget();
    leaf.unwrap();
    assert!(leaf_used < used);
    let tight = leaf_used + (used - leaf_used) / 2;
    tc::set_declaration_budget(tight);
    let constrained = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &i,
        &s,
    );
    let exhausted = tc::declaration_budget_exhausted();
    let unchanged_limit = tc::declaration_budget_limit();
    tc::clear_declaration_budget();
    let reason = constrained.expect_err("complete family must share the original caller pot");
    assert!(exhausted);
    assert_eq!(unchanged_limit, tight);
    eprintln!(
        "same-island leaf={leaf_used}, full={used}, tight={tight}; causal aggregate refusal: {reason}"
    );
    tc::set_declaration_budget(cap + 1);
    let result = certify_source_bound_call_family(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        &i,
        &s,
    );
    let remaining = tc::declaration_budget_remaining();
    let limit = tc::declaration_budget_limit();
    tc::clear_declaration_budget();
    assert!(
        result
            .unwrap_err()
            .contains("cannot replace a larger active caller")
    );
    assert_eq!(remaining, cap + 1);
    assert_eq!(limit, cap + 1);
}

#[cfg(feature = "source-value-operational")]
#[path = "source_bound_calls/readonly.rs"]
mod readonly;
