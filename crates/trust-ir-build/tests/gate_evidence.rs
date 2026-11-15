// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Roadmap WS1.12(c) / WS6.7(b): a `BodyGate::Gated` license may carry
//! `GateEvidence { obligation, body_digest }` (binary v61, tag 3), and a
//! PRESENT evidence is never taken on faith.
//!
//! * POSITIVE: a kernel-TV-certified body whose license cites its TV row and
//!   the body's `Module::function_body_digest` is admitted by every lane —
//!   structural, codegen, and codegen under `with_gate_evidence(true)`.
//! * NEGATIVE TWINS (each refused by its NAMED error):
//!   - the body edited after the license was stamped (an unused constant, so
//!     the kernel TV still re-checks and the ONLY defect is the stale digest)
//!     → `GatedEvidenceMismatch`;
//!   - evidence citing another function's row, a row that is not a Certified
//!     TranslationValidation obligation, or no row → `GatedEvidenceMismatch`;
//!   - an evidence-bound license with NO evidence under the evidence policy →
//!     `UnevidencedGate` (the default lanes keep admitting it — `None` is NO
//!     EVIDENCE RECORDED, the meaning of every pre-v61 license).
//! * MUTATION CONTROL (roadmap WS6.7: transplant a minted license onto a
//!   sibling with the same signature and body): refused by the cited row's
//!   function scope AND by the body digest, which binds the function's own
//!   identity.
//! * Controls: a non-evidence-bound authority needs no evidence under the
//!   policy; stamping the evidence never moves the digest it cites.
//!
//! FEATURES. The rules are feature-free (gate 9 runs this file with no
//! features); the binary / serde transport assertions sit behind
//! `#[cfg(feature = ..)]` exactly as in `certificate_binding.rs`.

use trust_ir::inst::{BinOp, Inst};
use trust_ir::proof::{
    ObligationKind, ProofDigest, ProofLineageId, ProofObligation, ProofStatus, ProofTransform,
    ProofTransformStage,
};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir::{BodyGate, FuncId, GateEvidence, InstrNode, Module, Producer};
use trust_ir_build::{
    ModuleBuilder, ValidationConfig, ValidationError, certify_identity_lineage_rung,
    validate_module, validate_module_for_codegen, validate_module_with_config,
};

const TV: &str = "clean-kernel-tv";

/// `f(a, b) = a*b + a` and its byte-identical twin `g`; both U64, Clean.
fn base() -> Module {
    let mut mb = ModuleBuilder::new("gate_evidence");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    for name in ["f", "g"] {
        let mut fb = mb.function(name, sig);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::U64);
        let b = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let p = fb.mul(Ty::U64, a, b);
        let r = fb.binop(BinOp::Add, Ty::U64, p, a);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn fid(m: &Module, name: &str) -> FuncId {
    m.functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function `{name}`"))
        .id
}

/// Certify `names[i]` as obligation `i` (kernel-replayable identity rung).
fn certify(m: &mut Module, names: &[&str]) {
    for (i, name) in names.iter().enumerate() {
        let id = u32::try_from(i).expect("small fixture");
        let (_, obligation, certificate) = certify_identity_lineage_rung(
            m,
            ProofLineageId::new(id),
            ProofId::new(id),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "identity",
                "gate-evidence",
                "1.0.0",
            ),
            fid(m, name),
        )
        .expect("fixture body is in the backend-TV fragment");
        m.proof_obligations.push(obligation);
        m.proof_certificates.push(certificate);
    }
}

/// License `name` by `authority`, citing `obligation` and the body's digest
/// NOW (`evidence = false`: no evidence recorded).
fn license(m: &mut Module, name: &str, authority: &str, obligation: Option<u32>) {
    let id = fid(m, name);
    let evidence = obligation.map(|o| GateEvidence {
        obligation: ProofId::new(o),
        body_digest: m.function_body_digest(id).expect("the body has a digest"),
    });
    m.function_by_id_mut(id).expect("present").body_gate = Some(BodyGate::Gated {
        authority: authority.to_string(),
        evidence,
    });
}

/// `f` and `g` certified (#0, #1) and each licensed with evidence.
fn honest() -> Module {
    let mut m = base();
    certify(&mut m, &["f", "g"]);
    license(&mut m, "f", TV, Some(0));
    license(&mut m, "g", TV, Some(1));
    m
}

fn strict() -> ValidationConfig<'static> {
    ValidationConfig::pinned()
        .with_codegen(true)
        .with_gate_evidence(true)
}

fn evidence_mismatches(errors: &[ValidationError], function: FuncId) -> Vec<String> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::GatedEvidenceMismatch {
                function: f,
                detail,
            } if *f == function.index() => Some(detail.clone()),
            _ => None,
        })
        .collect()
}

#[test]
fn evidenced_license_is_admitted_by_every_lane() {
    let m = honest();
    assert_eq!(validate_module(&m), Vec::new());
    assert_eq!(validate_module_for_codegen(&m), Vec::new());
    assert_eq!(
        validate_module_with_config(&m, &strict()).into_errors(),
        Vec::new()
    );
}

/// Stamping the license (and its evidence) never moves the digest it cites:
/// the body digest excludes the codegen license, exactly as the executable
/// projection does.
#[test]
fn stamping_the_evidence_does_not_move_the_body_digest() {
    let unlicensed = {
        let mut m = base();
        certify(&mut m, &["f", "g"]);
        m
    };
    let licensed = honest();
    for name in ["f", "g"] {
        assert_eq!(
            unlicensed.function_body_digest(fid(&unlicensed, name)),
            licensed.function_body_digest(fid(&licensed, name)),
            "`{name}`"
        );
    }
    // ... while a different body digests apart, even with the same shape.
    assert_ne!(
        licensed.function_body_digest(fid(&licensed, "f")),
        licensed.function_body_digest(fid(&licensed, "g")),
        "the digest binds the function's own identity"
    );
}

/// NEGATIVE TWIN (roadmap: stale body digest — edit the body after mint): an
/// unused constant leaves the kernel TV re-checking, so the ONLY defect is the
/// license naming the old body, refused as `GatedEvidenceMismatch`.
#[test]
fn stale_body_digest_is_refused() {
    let mut m = honest();
    let f = fid(&m, "f");
    let func = m.function_by_id_mut(f).expect("present");
    let fresh = trust_ir::ValueId::new(
        func.blocks
            .iter()
            .flat_map(|b| {
                b.params.iter().map(|(v, _)| v.index()).chain(
                    b.body
                        .iter()
                        .flat_map(|n| n.results.iter().map(|v| v.index())),
                )
            })
            .max()
            .map_or(0, |max| max + 1),
    );
    func.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: trust_ir::constant::Constant::Int(9),
        })
        .with_result(fresh),
    );
    let errors = validate_module(&m);
    let details = evidence_mismatches(&errors, f);
    assert!(
        details.iter().any(|d| d.contains("another body")),
        "{errors:?}"
    );
    assert!(
        !errors.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { .. }
        )),
        "control: the kernel TV still re-checks, so the digest is the only defect: {errors:?}"
    );
}

/// NEGATIVE TWINS: the cited obligation must be THIS function's Certified TV
/// row.
#[test]
fn evidence_citing_the_wrong_row_is_refused() {
    let f_id = {
        let m = honest();
        fid(&m, "f")
    };
    // (i) g's row.
    let mut m = honest();
    license(&mut m, "f", TV, Some(1));
    assert!(
        evidence_mismatches(&validate_module(&m), f_id).iter().any(
            |d| d.contains("not a Certified TranslationValidation row scoped to this function")
        ),
        "{:?}",
        validate_module(&m)
    );
    // (ii) no such row.
    let mut m = honest();
    license(&mut m, "f", TV, Some(77));
    assert!(
        evidence_mismatches(&validate_module(&m), f_id)
            .iter()
            .any(|d| d.contains("does not declare"))
    );
    // (iii) a Pending TV row scoped to f.
    let mut m = base();
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "pending TV",
        )
        .with_function(f_id),
    );
    license(&mut m, "f", TV, Some(0));
    assert!(
        evidence_mismatches(&validate_module(&m), f_id)
            .iter()
            .any(|d| d.contains("not a Certified TranslationValidation row")),
        "{:?}",
        validate_module(&m)
    );
}

/// NEGATIVE TWINS (review): three more rows the evidence must not accept —
/// a `Certified` row of another KIND scoped to `f`, a TranslationValidation
/// row scoped to `f` at a tier below `Certified` (`Discharged`), and a cited
/// id the module declares TWICE (the one row it names is ambiguous).
#[test]
fn evidence_citing_a_row_of_the_wrong_kind_tier_or_identity_is_refused() {
    let f_id = fid(&honest(), "f");
    for (kind, status, what) in [
        (
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "a Certified Postcondition",
        ),
        (
            ObligationKind::TranslationValidation,
            ProofStatus::Discharged,
            "a Discharged TranslationValidation row",
        ),
    ] {
        let mut m = base();
        m.proof_obligations
            .push(ProofObligation::new(ProofId::new(0), kind, status, what).with_function(f_id));
        license(&mut m, "f", TV, Some(0));
        assert!(
            evidence_mismatches(&validate_module(&m), f_id)
                .iter()
                .any(|d| d.contains("not a Certified TranslationValidation row")),
            "{what}: {:?}",
            validate_module(&m)
        );
    }
    let mut m = honest();
    let duplicate = m.proof_obligations[0].clone();
    m.proof_obligations.push(duplicate);
    assert!(
        evidence_mismatches(&validate_module(&m), f_id)
            .iter()
            .any(|d| d.contains("more than once")),
        "{:?}",
        validate_module(&m)
    );
}

/// NEGATIVE TWIN (review): the body digest is compared as a whole
/// `ProofDigest` — the SAME 32 bytes under another algorithm tag name another
/// digest, and are refused.
#[test]
fn evidence_digest_under_another_algorithm_tag_is_refused() {
    use trust_ir::proof::ProofDigestAlgorithm;
    let mut m = honest();
    let f = fid(&m, "f");
    let Some(BodyGate::Gated {
        evidence: Some(evidence),
        ..
    }) = &mut m.function_by_id_mut(f).expect("f").body_gate
    else {
        panic!("honest() licenses f with evidence");
    };
    assert_eq!(evidence.body_digest.algorithm, ProofDigestAlgorithm::Sha256);
    evidence.body_digest.algorithm = ProofDigestAlgorithm::TrustIrStableV1;
    assert!(
        evidence_mismatches(&validate_module(&m), f)
            .iter()
            .any(|d| d.contains("another body")),
        "{:?}",
        validate_module(&m)
    );
}

/// Evidence is never taken on faith WHATEVER THE AUTHORITY (review): the
/// license rules read evidence only for an evidence-bound authority, so a
/// check hung off them would let `trust-verify` carry any evidence at all.
/// Under a non-evidence-bound authority, the same true evidence is accepted
/// (control) and a stale one is refused on the structural lane.
#[test]
fn evidence_is_checked_under_every_authority() {
    let mut m = honest();
    let f = fid(&m, "f");
    let gate = &mut m.function_by_id_mut(f).expect("f").body_gate;
    let Some(BodyGate::Gated { authority, .. }) = gate else {
        panic!("honest() licenses f");
    };
    *authority = "trust-verify".to_string();
    assert!(
        evidence_mismatches(&validate_module(&m), f).is_empty(),
        "control: true evidence under another authority holds: {:?}",
        validate_module(&m)
    );
    let Some(BodyGate::Gated {
        evidence: Some(evidence),
        ..
    }) = &mut m.function_by_id_mut(f).expect("f").body_gate
    else {
        panic!("still evidenced");
    };
    evidence.body_digest.bytes[0] ^= 1;
    assert!(
        evidence_mismatches(&validate_module(&m), f)
            .iter()
            .any(|d| d.contains("another body")),
        "{:?}",
        validate_module(&m)
    );
}

/// NEGATIVE TWIN: an evidence-bound license with NO evidence is refused by
/// the evidence policy, by name — and admitted by the default lanes.
#[test]
fn evidence_free_bound_license_is_refused_only_by_the_policy() {
    let mut m = base();
    certify(&mut m, &["f", "g"]);
    license(&mut m, "f", TV, None);
    license(&mut m, "g", TV, Some(1));
    assert_eq!(validate_module_for_codegen(&m), Vec::new());
    let errors = validate_module_with_config(&m, &strict()).into_errors();
    assert_eq!(
        errors,
        vec![ValidationError::UnevidencedGate {
            function: fid(&m, "f").index(),
            authority: TV.to_string(),
        }]
    );
}

/// CONTROL (review): the evidence policy is about licensed BODIES. A
/// bodyless declaration carrying an evidence-free `clean-kernel-tv` license is
/// not what `UnevidencedGate` names (there is no body a digest could state),
/// while the defined twin under the same license is.
#[test]
fn evidence_policy_names_bodies_not_declarations() {
    let mut m = base();
    let sig = m.functions[0].ty;
    let mut decl = trust_ir::Function::new(
        FuncId::new(u32::try_from(m.functions.len()).expect("small")),
        "extern_h",
        sig,
        trust_ir::BlockId::new(0),
    );
    decl.linkage = trust_ir::Linkage::External;
    decl.body_gate = Some(BodyGate::gated(TV));
    let decl_id = decl.id;
    m.try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
    license(&mut m, "f", TV, None);
    let unevidenced: Vec<u32> = validate_module_with_config(&m, &strict())
        .into_errors()
        .into_iter()
        .filter_map(|e| match e {
            ValidationError::UnevidencedGate { function, .. } => Some(function),
            _ => None,
        })
        .collect();
    assert!(
        unevidenced.contains(&fid(&m, "f").index()),
        "{unevidenced:?}"
    );
    assert!(!unevidenced.contains(&decl_id.index()), "{unevidenced:?}");
}

/// CONTROL: an authority that is not evidence-bound needs no evidence under
/// the policy.
#[test]
fn unbound_authority_needs_no_evidence() {
    let mut m = base();
    license(&mut m, "f", "trust-verify", None);
    license(&mut m, "g", "trust-verify", None);
    assert!(
        !validate_module_with_config(&m, &strict())
            .into_errors()
            .iter()
            .any(|e| matches!(e, ValidationError::UnevidencedGate { .. }))
    );
}

/// MUTATION CONTROL (roadmap WS6.7: transplant onto a sibling with the same
/// signature): `g` has `f`'s body byte for byte, yet `f`'s license moved onto
/// `g` is refused twice — the cited row is scoped to `f`, and the digest
/// binds `f`'s own identity.
#[test]
fn transplanted_license_is_refused_by_scope_and_digest() {
    let mut m = honest();
    let f = fid(&m, "f");
    let g = fid(&m, "g");
    let transplanted = m.function_by_id_mut(f).expect("f").body_gate.clone();
    m.function_by_id_mut(g).expect("g").body_gate = transplanted;
    let details = evidence_mismatches(&validate_module(&m), g);
    assert!(
        details.iter().any(
            |d| d.contains("not a Certified TranslationValidation row scoped to this function")
        ),
        "{details:?}"
    );
    assert!(
        details.iter().any(|d| d.contains("another body")),
        "{details:?}"
    );
}

/// The body digest is refused, never panics, for a body with no identity.
#[test]
fn function_body_digest_refuses_a_missing_function() {
    let m = base();
    assert!(m.function_body_digest(FuncId::new(99)).is_err());
    assert!(
        m.function_body_digest(fid(&m, "f"))
            .is_ok_and(|d| d != ProofDigest::zero())
    );
}

/// A body spelling the producer-internal `Ty::Error` has no digest (the
/// binary writer panics on it). Evidence on such a body is REFUSED by name —
/// beside the error-type refusal itself — and the validator does not crash.
#[test]
fn evidence_on_an_undigestable_body_is_refused_not_a_crash() {
    let mut m = honest();
    let f = fid(&m, "f");
    let func = m.function_by_id_mut(f).expect("present");
    func.blocks[0].params[0].1 = Ty::Error;
    let errors = validate_module(&m);
    assert!(
        evidence_mismatches(&errors, f)
            .iter()
            .any(|d| d.contains("Ty::Error")),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// Amendment D ("Body digest"; ruling WA-3): `trust_ir.function.body.v1` binds,
// per body, the drop-glue rows its drops resolve to. A drop executes as a
// call of its glue, so the glue is part of what the licensed body RUNS: a
// table edit that changes which glue one of its drops calls must move the
// digest, and a license citing the old digest must be refused.
// ---------------------------------------------------------------------------

/// Three owning structs `S0..S2` (`{ data: ptr }`), the glue signature
/// `(ptr) -> ()`, three defined glues `drop_a` @func.0, `drop_b` @func.1,
/// `drop_c` @func.2 (each `ret`), and `caller` @func.3 whose body is
/// `sites` then `ret`. The drop-glue table is EMPTY: tests state the rows.
fn drop_module(sites: &[(bool, u32)]) -> Module {
    use trust_ir::ty::{FieldDef, FuncTy, StructDef, StructRepr};
    use trust_ir::value::{StructId, ValueId};
    use trust_ir::{Block, BlockId, Function};
    let mut m = Module::new("drop_body_digest");
    for id in 0..3 {
        m.add_struct(StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: vec![FieldDef {
                name: "data".into(),
                ty: Ty::Ptr,
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::default(),
            origin: None,
        });
    }
    let sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (id, name) in [(0, "drop_a"), (1, "drop_b"), (2, "drop_c"), (3, "caller")] {
        let mut f = Function::new(FuncId::new(id), name, sig, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.params.push((ValueId::new(0), Ty::Ptr));
        if name == "caller" {
            for (k, &(invoke, ty)) in sites.iter().enumerate() {
                let ty = Ty::Struct(StructId::new(ty));
                let ptr = ValueId::new(0);
                // Each `DropInvoke` continues at a fresh block; the digest
                // reads the instruction, not the CFG's validity.
                let next = BlockId::new(u32::try_from(k).expect("small") + 1);
                entry.body.push(InstrNode::new(if invoke {
                    Inst::DropInvoke {
                        ty,
                        ptr,
                        normal_dest: next,
                        normal_args: vec![],
                        unwind_dest: next,
                    }
                } else {
                    Inst::Drop { ty, ptr }
                }));
            }
        }
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(entry);
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
    }
    m
}

fn s(id: u32) -> Ty {
    Ty::Struct(trust_ir::value::StructId::new(id))
}

const CALLER: u32 = 3;

fn body_digest(m: &Module, f: u32) -> ProofDigest {
    m.function_body_digest(FuncId::new(f))
        .expect("the body has a digest")
}

/// Every edit of the row a drop resolves through moves the digest: register
/// glue for an unresolved drop, re-point the row at another glue, remove it.
/// Rows the body's drops do not resolve through never move it (controls).
#[test]
fn body_digest_binds_the_drop_glue_its_drops_resolve_to() {
    for invoke in [false, true] {
        let unresolved = drop_module(&[(invoke, 0)]);
        let mut resolved = unresolved.clone();
        resolved.set_drop_glue(s(0), FuncId::new(0)).unwrap();
        let mut repointed = unresolved.clone();
        repointed.set_drop_glue(s(0), FuncId::new(2)).unwrap();
        let mut unrelated = resolved.clone();
        unrelated.set_drop_glue(s(1), FuncId::new(1)).unwrap();

        let d_unresolved = body_digest(&unresolved, CALLER);
        let d_resolved = body_digest(&resolved, CALLER);
        let d_repointed = body_digest(&repointed, CALLER);
        assert_ne!(
            d_unresolved, d_resolved,
            "registering glue (invoke={invoke})"
        );
        assert_ne!(
            d_resolved, d_repointed,
            "re-pointing glue (invoke={invoke})"
        );
        assert_ne!(d_unresolved, d_repointed, "invoke={invoke}");
        // Control: a row for a type this body never drops is not bound.
        assert_eq!(
            d_resolved,
            body_digest(&unrelated, CALLER),
            "invoke={invoke}"
        );
        // Control: a body with no drops keeps the digest it has with no
        // table at all, whatever the table says.
        for glue in 0..3 {
            assert_eq!(
                body_digest(&unresolved, glue),
                body_digest(&unrelated, glue),
                "glue @func.{glue} has no drops (invoke={invoke})"
            );
        }
    }
    // The site's spelling is part of the body: a `Drop` and a `DropInvoke`
    // at the same type, through the same row, are different bodies.
    let mut plain = drop_module(&[(false, 0)]);
    plain.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    let mut invoking = drop_module(&[(true, 0)]);
    invoking.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    assert_ne!(body_digest(&plain, CALLER), body_digest(&invoking, CALLER));
}

/// One row per resolved TYPE, whatever the number or order of sites: two
/// drops of `S0` bind one row, and the bound rows follow the table's
/// canonical order, so a table that lists the same rows binds the same
/// digest however it was built.
#[test]
fn body_digest_binds_each_resolved_row_once_in_canonical_order() {
    let mut twice = drop_module(&[(false, 1), (false, 0), (false, 1)]);
    twice.set_drop_glue(s(1), FuncId::new(1)).unwrap();
    twice.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    let mut built_other_way = drop_module(&[(false, 1), (false, 0), (false, 1)]);
    built_other_way.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    built_other_way.set_drop_glue(s(1), FuncId::new(1)).unwrap();
    assert_eq!(twice.drop_glue, built_other_way.drop_glue);
    assert_eq!(
        body_digest(&twice, CALLER),
        body_digest(&built_other_way, CALLER)
    );
    // Swapping which glue destroys which type is a different body.
    let mut swapped = drop_module(&[(false, 1), (false, 0), (false, 1)]);
    swapped.set_drop_glue(s(1), FuncId::new(0)).unwrap();
    swapped.set_drop_glue(s(0), FuncId::new(1)).unwrap();
    assert_ne!(body_digest(&twice, CALLER), body_digest(&swapped, CALLER));
}

/// A malformed table states no single destructor for the body's drops, so
/// the body has no identity: a site type two rows name, or one glue named
/// for two of the body's site types, is refused (never a digest over a
/// guessed row). A malformed row the body does not resolve through does not
/// block its digest.
#[test]
fn body_digest_refuses_a_drop_through_a_malformed_table() {
    use trust_ir::DropGlueEntry;
    let mut ambiguous = drop_module(&[(false, 0)]);
    ambiguous.drop_glue = vec![
        DropGlueEntry {
            glue: FuncId::new(0),
            ty: s(0),
        },
        DropGlueEntry {
            glue: FuncId::new(2),
            ty: s(0),
        },
    ];
    let error = ambiguous
        .function_body_digest(FuncId::new(CALLER))
        .expect_err("two rows name S0");
    assert!(error.contains("two or more drop-glue rows"), "{error}");
    // The glue bodies drop nothing, so they keep a digest.
    assert!(ambiguous.function_body_digest(FuncId::new(0)).is_ok());

    let mut shared = drop_module(&[(false, 0), (false, 1)]);
    shared.drop_glue = vec![
        DropGlueEntry {
            glue: FuncId::new(0),
            ty: s(0),
        },
        DropGlueEntry {
            glue: FuncId::new(0),
            ty: s(1),
        },
    ];
    let error = shared
        .function_body_digest(FuncId::new(CALLER))
        .expect_err("one glue for S0 and S1");
    assert!(error.contains("through the one glue"), "{error}");
    // Control: a caller dropping only one of the two types resolves through
    // one row and has a digest.
    let mut one = shared.clone();
    one.functions[3].blocks[0].body.remove(1);
    assert!(one.function_body_digest(FuncId::new(CALLER)).is_ok());
}

/// The license rule end to end: evidence stamped while `S0` resolved to
/// `drop_a` is refused once the table re-points `S0` at `drop_c`, or drops
/// the row — the body text is unchanged, what it runs is not. Evidence over
/// a drop through a malformed table is refused by name, never a crash.
#[test]
fn evidence_is_refused_when_the_glue_a_drop_resolves_to_changes() {
    let mut m = drop_module(&[(false, 0)]);
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    let caller = FuncId::new(CALLER);
    let stamped = GateEvidence {
        obligation: ProofId::new(0),
        body_digest: body_digest(&m, CALLER),
    };
    m.function_by_id_mut(caller).expect("caller").body_gate = Some(BodyGate::Gated {
        authority: "trust-verify".to_string(),
        evidence: Some(stamped),
    });
    // A row for the evidence to cite. Its tier is not this test's subject:
    // only the digest detail (`another body`) is asserted below.
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "caller TV",
        )
        .with_function(caller),
    );
    let holds = |m: &Module| {
        !evidence_mismatches(&validate_module(m), caller)
            .iter()
            .any(|d| d.contains("another body"))
    };
    assert!(holds(&m), "control: {:?}", validate_module(&m));

    let mut repointed = m.clone();
    repointed.drop_glue.clear();
    repointed.set_drop_glue(s(0), FuncId::new(2)).unwrap();
    assert!(!holds(&repointed), "{:?}", validate_module(&repointed));

    let mut removed = m.clone();
    removed.drop_glue.clear();
    assert!(!holds(&removed), "{:?}", validate_module(&removed));

    // Control: registering glue for a type the caller never drops keeps it.
    let mut unrelated = m.clone();
    unrelated.set_drop_glue(s(1), FuncId::new(1)).unwrap();
    assert!(holds(&unrelated), "{:?}", validate_module(&unrelated));

    let mut ambiguous = m.clone();
    ambiguous.drop_glue.push(trust_ir::DropGlueEntry {
        glue: FuncId::new(2),
        ty: s(0),
    });
    let errors = validate_module(&ambiguous);
    assert!(
        evidence_mismatches(&errors, caller)
            .iter()
            .any(|d| d.contains("two or more drop-glue rows")),
        "{errors:?}"
    );
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidDropGlue { .. })),
        "{errors:?}"
    );
}

/// The license and its evidence survive every carrying format.
#[cfg(feature = "binary")]
#[test]
fn evidenced_license_round_trips_the_binary_codec() {
    use trust_ir::binary::{
        CERTIFICATE_BINDING_FORMAT_VERSION, deserialize_module, serialize_module,
    };
    let m = honest();
    let bytes = serialize_module(&m).expect("an evidenced license is encodable");
    assert_eq!(
        &bytes[8..12],
        &CERTIFICATE_BINDING_FORMAT_VERSION.to_le_bytes(),
        "an evidenced license selects the carrier's version"
    );
    let back = deserialize_module(&bytes).expect("decodes");
    assert_eq!(back, m);
    assert_eq!(validate_module(&back), Vec::new());
}
