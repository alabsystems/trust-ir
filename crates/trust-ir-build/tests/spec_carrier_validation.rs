// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Wire v46 — the typed spec carrier (roadmap WS4.14, F-014): the VALIDATOR
// half. The format half (codecs, version selection, digests, the S4 rules of
// `validate_spec_structure`) is `trust-ir/tests/spec_carrier.rs`.
//
// What is pinned here:
//
// * the two `ClausePlace` leaks the roadmap's REVIEW names — a function
//   summary clause binding `SpecVar` (`InvalidFunctionSummary`) and a module
//   obligation binding `SpecVarNext` (`InvalidObligationBinding`) — with the
//   pre-existing places as mutation control;
// * the obligation `spec` backref resolves to exactly one declared temporal
//   property of exactly one machine, on a temporal kind only
//   (`UnresolvedObligationSpecRef`);
// * the S4 structural refusals surface through `validate_module` as
//   `InvalidSpecStructure`;
// * `kernel_certified_theorems` — the ONE minter of the `CleanTheorem`
//   witness — projects only certificates the kernel actually replayed, and
//   nothing from an invalid module, so a hand-written `Certified` row earns
//   no theorem;
// * the three archived proof-program rows this increment ports (test names
//   spell the row ids with `_`).

use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofEvidence, ProofFormula,
    ProofLineageId, ProofObligation, ProofStatus, ProofTransform, ProofTransformStage,
    SpecObligationRef, clean_cic_lineage_digest,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{
    BodyGate, FunctionSummary, KernelCertifiedTheorems, Module, Producer, ProofKind,
    SpecEnforcementMode, SpecInvariant, SpecLinkOptions, SpecLinkViolation, SpecModule, SpecProof,
    SpecTemporal, SpecVar, SpecWaiver, TemporalForm, link_spec_modules_with_theorems,
};
use trust_ir_build::{
    ModuleBuilder, ValidationError, certify_identity_lineage_rung, kernel_certified_theorems,
    validate_module,
};

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn bind(name: &str, sort: ClauseSort, place: ClausePlace) -> (String, ClauseBinding) {
    (name.to_string(), ClauseBinding { sort, place })
}

fn formula(text: &str, bindings: Vec<(String, ClauseBinding)>) -> ProofFormula {
    let mut f = ProofFormula::smtlib2(text, "Bool");
    f.bindings = bindings;
    f
}

/// `(<= seq 7)` over state variable 0.
fn bounded() -> ProofFormula {
    formula(
        "(<= seq 7)",
        vec![bind(
            "seq",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 0 },
        )],
    )
}

/// `(= seq 7)` over state variable 0.
fn full() -> ProofFormula {
    formula(
        "(= seq 7)",
        vec![bind(
            "seq",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 0 },
        )],
    )
}

/// `fn bump(x: i64) -> i64 { x + 1 }`.
fn bump_module() -> Module {
    let mut mb = ModuleBuilder::new("spec_carrier_validation");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("bump", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::I64, 1);
    let r = fb.add(Ty::I64, x, one);
    fb.ret(vec![r]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The typed `ring` machine (design-only: the S4 rules are structural and run
/// in both modes; L1 is not under test here).
fn typed_ring() -> SpecModule {
    let mut ring = SpecModule::design_only("ring");
    ring.vars = vec![SpecVar::new("seq", "0..7").with_sort(ClauseSort::Int)];
    ring.actions = vec!["Push".to_string(), "Pop".to_string()];
    ring.invariants = vec![SpecInvariant::new("BoundedSeq", "(<= seq 7)").with_typed(bounded())];
    ring.temporal = vec![
        SpecTemporal::new("AlwaysBounded", TemporalForm::Always(bounded())),
        SpecTemporal::new("EventuallyFull", TemporalForm::Eventually(full())),
    ];
    ring
}

fn liveness(id: u32, machine: &str, temporal: &str) -> ProofObligation {
    let mut o = ProofObligation::new(
        ProofId::new(id),
        ObligationKind::Liveness,
        ProofStatus::Pending,
        "eventually the ring is full",
    )
    .with_formula(full());
    o.spec = Some(SpecObligationRef::new(machine, temporal));
    o
}

fn ring_module() -> Module {
    let mut m = bump_module();
    m.spec_modules.push(typed_ring());
    m.proof_obligations
        .push(liveness(0, "ring", "EventuallyFull"));
    m
}

fn assert_clean(module: &Module) {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "expected a clean module, got {errors:?}");
}

fn spec_ref_errors(module: &Module) -> Vec<(u32, String, String, &'static str)> {
    validate_module(module)
        .into_iter()
        .filter_map(|e| match e {
            ValidationError::UnresolvedObligationSpecRef {
                obligation,
                machine,
                temporal,
                reason,
            } => Some((obligation, machine, temporal, reason)),
            _ => None,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// REVIEW — the new `ClausePlace` tags leak into existing surfaces
// ---------------------------------------------------------------------------

/// A summary `ensures` binding `SpecVar { 0 }` is `InvalidFunctionSummary` by
/// name; the same clause bound to `Param { 0 }` is the mutation control.
#[test]
fn summary_clause_binding_a_spec_variable_is_an_invalid_function_summary() {
    let refused = {
        let mut m = bump_module();
        m.functions[0].summary = Some(
            FunctionSummary::new()
                .with_params(vec!["x".to_string()])
                .ensuring(formula(
                    "(bvsge x #x0000000000000000)",
                    vec![bind(
                        "x",
                        ClauseSort::BitVec(64),
                        ClausePlace::SpecVar { index: 0 },
                    )],
                )),
        );
        m
    };
    let errors = validate_module(&refused);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidFunctionSummary { function: 0, detail }
                if detail.contains("names SpecVar 0, a spec-machine state variable")
                    && detail.contains("a function summary has none")
        )),
        "{errors:?}"
    );
    // `SpecVarNext` is refused the same way.
    let mut primed = refused.clone();
    primed.functions[0].summary.as_mut().unwrap().ensures[0].bindings[0]
        .1
        .place = ClausePlace::SpecVarNext { index: 0 };
    assert!(validate_module(&primed).iter().any(|e| matches!(
        e,
        ValidationError::InvalidFunctionSummary { detail, .. }
            if detail.contains("names SpecVarNext 0, a spec-machine state variable")
    )));

    // Mutation control: the signature place resolves.
    let mut control = refused;
    control.functions[0].summary.as_mut().unwrap().ensures[0].bindings[0]
        .1
        .place = ClausePlace::Param { index: 0 };
    assert_clean(&control);
}

/// A module obligation binding `SpecVarNext { 0 }` is `InvalidObligationBinding`
/// by name; the same formula bound to a signature place is not (no other rule
/// reads a module obligation's bindings today — WS4.4 territory).
#[test]
fn module_obligation_binding_a_spec_variable_is_an_invalid_obligation_binding() {
    let obligation = |place: ClausePlace| {
        let mut m = bump_module();
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Postcondition,
                ProofStatus::Pending,
                "result stays in range",
            )
            .with_function(FuncId::new(0))
            .with_formula(formula("(<= r 7)", vec![bind("r", ClauseSort::Int, place)])),
        );
        m
    };
    let errors = validate_module(&obligation(ClausePlace::SpecVarNext { index: 0 }));
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::InvalidObligationBinding { obligation: 0, detail }]
                if detail.contains("binds \"r\" to SpecVarNext 0, a spec-machine state variable")
        ),
        "{errors:?}"
    );
    assert!(
        errors[0]
            .to_string()
            .starts_with("obligation #0: clause binding binds"),
        "{}",
        errors[0]
    );
    let errors = validate_module(&obligation(ClausePlace::SpecVar { index: 0 }));
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::InvalidObligationBinding { obligation: 0, .. }]
        ),
        "{errors:?}"
    );
    // Mutation control.
    assert_clean(&obligation(ClausePlace::ResultSlot { index: 0 }));
}

// ---------------------------------------------------------------------------
// The obligation `spec` backref
// ---------------------------------------------------------------------------

/// Positive: a `Liveness` obligation whose backref names a declared temporal
/// property of a declared machine validates (and so does `TemporalSafety`).
#[test]
fn a_resolving_spec_backref_validates_on_both_temporal_kinds() {
    assert_clean(&ring_module());
    let mut safety = ring_module();
    safety.proof_obligations[0].kind = ObligationKind::TemporalSafety;
    safety.proof_obligations[0].spec = Some(SpecObligationRef::new("ring", "AlwaysBounded"));
    safety.proof_obligations[0].formula = Some(bounded());
    assert_clean(&safety);
}

/// A backreferenced obligation's own spec-variable bindings are checked
/// against the machine it discharges a property of: an index past its `vars`,
/// a sort its declaration contradicts, and a primed `SpecVarNext` on a state
/// predicate are each `InvalidObligationBinding`; primed on a fairness action
/// relation is accepted (mutation control).
#[test]
fn a_backreferenced_obligation_binds_only_its_machines_variables() {
    let detail = |m: &Module| -> Vec<String> {
        validate_module(m)
            .into_iter()
            .filter_map(|e| match e {
                ValidationError::InvalidObligationBinding {
                    obligation: 0,
                    detail,
                } => Some(detail),
                _ => None,
            })
            .collect()
    };
    let mut out_of_range = ring_module();
    out_of_range.proof_obligations[0].formula = Some(formula(
        "(= seq 7)",
        vec![bind(
            "seq",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 1 },
        )],
    ));
    let details = detail(&out_of_range);
    assert!(
        details
            .iter()
            .any(|d| d.contains("but machine \"ring\" declares 1 state variable(s)")),
        "{details:?}"
    );

    let mut sort_clash = ring_module();
    sort_clash.proof_obligations[0].formula = Some(formula(
        "(= seq 7)",
        vec![bind(
            "seq",
            ClauseSort::Bool,
            ClausePlace::SpecVar { index: 0 },
        )],
    ));
    let details = detail(&sort_clash);
    assert!(
        details
            .iter()
            .any(|d| d.contains("at sort Bool, but the variable declares sort Int")),
        "{details:?}"
    );

    // The same clash with `SpecVar.sort` left unrecorded: the `"0..7"` tag
    // still reads as `Int` (`SpecVar::effective_sort`), so the strip is
    // refused all the same — an absent declaration is not a wildcard.
    let mut unrecorded = sort_clash;
    unrecorded.spec_modules[0].vars[0].sort = None;
    let details = detail(&unrecorded);
    assert!(
        details
            .iter()
            .any(|d| d.contains("at sort Bool, but the variable declares sort Int")),
        "{details:?}"
    );

    let mut primed = ring_module();
    primed.proof_obligations[0].formula = Some(formula(
        "(= seq_next 7)",
        vec![bind(
            "seq_next",
            ClauseSort::Int,
            ClausePlace::SpecVarNext { index: 0 },
        )],
    ));
    let details = detail(&primed);
    assert!(
        details.iter().any(|d| d.contains(
            "the SUCCESSOR state, but the temporal property \"EventuallyFull\" it discharges is a \
             eventually state predicate"
        )),
        "{details:?}"
    );

    // Mutation control: the same primed binding discharging a fairness
    // property (an action relation) is legal.
    let mut fair = primed;
    fair.spec_modules[0].temporal.push(SpecTemporal::new(
        "PushFair",
        TemporalForm::WeakFair {
            action: "Push".to_string(),
            relation: None,
        },
    ));
    fair.proof_obligations[0].spec = Some(SpecObligationRef::new("ring", "PushFair"));
    assert_clean(&fair);
}

/// Negative twins, one mutation each: a non-temporal kind, an undeclared
/// machine, an undeclared property, a property declared twice, and a machine
/// name carried twice — every one `UnresolvedObligationSpecRef` with its own
/// named reason, and never resolved to "the first match".
#[test]
fn a_dangling_or_ambiguous_spec_backref_is_refused_by_name() {
    let mut wrong_kind = ring_module();
    wrong_kind.proof_obligations[0].kind = ObligationKind::Postcondition;
    let errors = spec_ref_errors(&wrong_kind);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].3,
        "only a Liveness or TemporalSafety obligation states a temporal property"
    );

    let mut no_machine = ring_module();
    no_machine.proof_obligations[0].spec = Some(SpecObligationRef::new("rung", "EventuallyFull"));
    let errors = spec_ref_errors(&no_machine);
    assert_eq!(
        errors,
        vec![(
            0,
            "rung".to_string(),
            "EventuallyFull".to_string(),
            "no SpecModule of this module carries that machine name"
        )]
    );

    let mut no_property = ring_module();
    no_property.proof_obligations[0].spec = Some(SpecObligationRef::new("ring", "EventuallyEmpty"));
    let errors = spec_ref_errors(&no_property);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].3,
        "that machine declares no temporal property of that name"
    );

    let mut twice = ring_module();
    let dup = twice.spec_modules[0].temporal[1].clone();
    twice.spec_modules[0].temporal.push(dup);
    let errors = spec_ref_errors(&twice);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].3,
        "that machine declares the temporal property more than once"
    );
    // The duplication itself is reported by the structural pass too.
    assert!(validate_module(&twice).iter().any(|e| matches!(
        e,
        ValidationError::InvalidSpecStructure {
            violation: SpecLinkViolation::DuplicateMemberIdentity {
                member: "temporal",
                ..
            }
        }
    )));

    let mut ambiguous = ring_module();
    let second = ambiguous.spec_modules[0].clone();
    ambiguous.spec_modules.push(second);
    let errors = spec_ref_errors(&ambiguous);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].3, "the machine name is ambiguous in this module");

    let rendered = validate_module(&no_machine)
        .into_iter()
        .find(|e| matches!(e, ValidationError::UnresolvedObligationSpecRef { .. }))
        .unwrap()
        .to_string();
    assert!(
        rendered.contains("spec backref \"rung\"/\"EventuallyFull\" does not resolve"),
        "{rendered}"
    );
}

/// The S4 structural rules reach `validate_module` as `InvalidSpecStructure`.
#[test]
fn s4_typed_carrier_refusals_surface_through_validate_module() {
    let mut out_of_range = ring_module();
    out_of_range.spec_modules[0].invariants[0].typed = Some(formula(
        "(<= seq 7)",
        vec![bind(
            "seq",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 4 },
        )],
    ));
    let errors = validate_module(&out_of_range);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::InvalidSpecStructure {
                violation: SpecLinkViolation::SpecTypedBindingInvalid {
                    subject: "invariant", name, binding, detail, ..
                }
            }] if name == "BoundedSeq" && binding == "seq" && detail.contains("out of range")
        ),
        "{errors:?}"
    );

    let mut sort_clash = ring_module();
    sort_clash.spec_modules[0].vars[0].sort = Some(ClauseSort::Bool);
    let errors = validate_module(&sort_clash);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidSpecStructure {
                violation: SpecLinkViolation::SpecVariableSortMismatch { variable, .. }
            } if variable == "seq"
        )),
        "{errors:?}"
    );
}

/// S3 under `Linked` (v46): a typed carrier whose `smtlib` rendering does not
/// read over its own bindings is refused by the module validator by name;
/// the same module under `DesignOnly` is not read.
#[test]
fn s3_linked_typed_carrier_text_surfaces_through_validate_module() {
    let mut garbage = ring_module();
    garbage.spec_modules[0].enforcement = SpecEnforcementMode::Linked;
    garbage.spec_modules[0].invariants[0].typed = Some(formula(
        "(<= seq",
        vec![bind(
            "seq",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 0 },
        )],
    ));
    let errors = validate_module(&garbage);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidSpecStructure {
                violation: SpecLinkViolation::LinkedTypedCarrierUnparsed {
                    subject: "invariant", name, detail, ..
                }
            } if name == "BoundedSeq" && detail.contains("not one quantifier-free SMT-LIB2 term")
        )),
        "{errors:?}"
    );
    // Mutation control: the same text, bindings and machine under `DesignOnly`.
    garbage.spec_modules[0].enforcement = SpecEnforcementMode::DesignOnly;
    assert!(!validate_module(&garbage).iter().any(|e| matches!(
        e,
        ValidationError::InvalidSpecStructure {
            violation: SpecLinkViolation::LinkedTypedCarrierUnparsed { .. }
        }
    )));
}

/// S3 under `Linked` (v46): a typed invariant that reads as a DIFFERENT
/// predicate from its own string `formula` is refused by the module validator
/// by name; the same carrier bound under another name for the same variable
/// agrees, and the same module under `DesignOnly` is not read.
#[test]
fn s3_linked_typed_carrier_must_agree_with_its_formula_through_validate_module() {
    let disagrees = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::InvalidSpecStructure {
                violation: SpecLinkViolation::LinkedTypedCarrierDisagrees { invariant, detail, .. }
            } if invariant == "BoundedSeq" && detail.contains("(<= seq 8)") && detail.contains("(<= seq 7)")
        )
    };
    let mut twin = ring_module();
    twin.spec_modules[0].enforcement = SpecEnforcementMode::Linked;
    twin.spec_modules[0].invariants[0].typed = Some(formula(
        "(<= seq 8)",
        vec![bind(
            "seq",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 0 },
        )],
    ));
    let errors = validate_module(&twin);
    assert!(errors.iter().any(disagrees), "{errors:?}");

    // Renaming control: bound as `s`, the carrier still reads as `(<= seq 7)`.
    let mut renamed = ring_module();
    renamed.spec_modules[0].enforcement = SpecEnforcementMode::Linked;
    renamed.spec_modules[0].invariants[0].typed = Some(formula(
        "(<= s 7)",
        vec![bind(
            "s",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 0 },
        )],
    ));
    let errors = validate_module(&renamed);
    assert!(
        !errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidSpecStructure {
                violation: SpecLinkViolation::LinkedTypedCarrierDisagrees { .. }
            }
        )),
        "{errors:?}"
    );

    // Mutation control: the same twin under `DesignOnly` is not read.
    twin.spec_modules[0].enforcement = SpecEnforcementMode::DesignOnly;
    assert!(!validate_module(&twin).iter().any(disagrees));
}

// ---------------------------------------------------------------------------
// `kernel_certified_theorems` — the CleanTheorem witness minter
// ---------------------------------------------------------------------------

/// `plus(a, b) = a * b + a`, Clean-produced and gated, in the backend-TV
/// fragment so `certify_identity_lineage_rung` can mint a kernel-replayable
/// `CleanTV.plus.denotes`.
fn plus_module() -> Module {
    let mut mb = ModuleBuilder::new("spec_carrier_plus");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = mb.function("plus", sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let p = f.mul(Ty::U64, a, b);
    let r = f.add(Ty::U64, p, a);
    f.ret(vec![r]);
    f.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    for func in &mut m.functions {
        func.body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".to_string(),
            evidence: None,
        });
    }
    m
}

fn certified_plus_module() -> Module {
    let mut m = plus_module();
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "identity",
            "spec-carrier",
            "1.0.0",
        ),
        m.functions[0].id,
    )
    .expect("plus is in the backend-TV fragment");
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    m
}

/// A Linked machine whose only proof binding is the Clean theorem `name`, with
/// every action waived so the binding alone decides certification.
fn with_clean_theorem_binding(mut m: Module, name: &str) -> Module {
    let mut ring = SpecModule::linked("ring");
    ring.vars = vec![SpecVar::new("seq", "Int")];
    ring.actions = vec!["Push".to_string()];
    ring.invariants = vec![SpecInvariant::new("BoundedSeq", "(<= seq 7)")];
    ring.waivers = vec![SpecWaiver {
        machine: "ring".to_string(),
        action: "Push".to_string(),
        reason: "spec_carrier probe".to_string(),
    }];
    ring.proofs = vec![SpecProof {
        machine: "ring".to_string(),
        action: "Push".to_string(),
        proof_name: "ring_push_refines".to_string(),
        kind: ProofKind::CleanTheorem {
            name: name.to_string(),
        },
    }];
    m.spec_modules.push(ring);
    m
}

/// Positive: the witness of a valid module names exactly the theorems whose
/// certificates the validator replayed; a valid module with no certificate
/// yields an EMPTY witness.
#[test]
fn kernel_certified_theorems_projects_exactly_the_replayed_certificates() {
    let witness = kernel_certified_theorems(&certified_plus_module()).expect("valid module");
    assert_eq!(witness.iter().collect::<Vec<_>>(), ["CleanTV.plus.denotes"]);
    assert_eq!(witness.len(), 1);
    assert!(witness.contains("CleanTV.plus.denotes"));

    let empty = kernel_certified_theorems(&plus_module()).expect("valid module");
    assert!(empty.is_empty());
    assert_eq!(empty, KernelCertifiedTheorems::default());
}

/// Negative twin: a module that merely WRITES `Certified` beside a hand-made
/// `CleanCic` certificate citing the theorem does not validate, so it gets no
/// witness at all — `Certified` is earned by the kernel re-check alone.
#[test]
fn a_hand_written_certified_row_earns_no_theorem() {
    let mut forged = certified_plus_module();
    // Keep the status, the lineage and the recheck directive; replace the
    // kernel proof term with bytes the kernel never produced.
    let ProofEvidence::CleanCic { term, .. } = &mut forged.proof_certificates[0].evidence else {
        unreachable!("the minter emits CleanCic");
    };
    *term = vec![0xde, 0xad, 0xbe, 0xef];
    let errors = kernel_certified_theorems(&forged).expect_err("a forged term does not validate");
    assert!(!errors.is_empty());

    // And a `Certified` row with no certificate at all.
    let mut bare = certified_plus_module();
    bare.proof_certificates.clear();
    assert!(kernel_certified_theorems(&bare).is_err());

    // Sanity: the lineage of the genuine certificate is the obligation's.
    let genuine = certified_plus_module();
    assert_eq!(
        genuine.proof_certificates[0].evidence.clean_cic_lineage(),
        Some(clean_cic_lineage_digest(&genuine.proof_obligations[0]))
    );
}

/// End to end: a Linked machine binding the kernel-established theorem
/// certifies through the linker with the minted witness; binding another name
/// is `CleanTheoremUnresolved`; and the SAME module with the certificate forged
/// certifies nothing, because there is no witness to resolve against.
#[test]
fn clean_theorem_binding_certifies_only_with_the_minted_witness() {
    let m = with_clean_theorem_binding(certified_plus_module(), "CleanTV.plus.denotes");
    let witness = kernel_certified_theorems(&m).expect("valid module");
    let report =
        link_spec_modules_with_theorems(&m, None, Some(&witness), SpecLinkOptions::default())
            .unwrap();
    assert!(report.is_certifying(), "{report:?}");

    let other = with_clean_theorem_binding(certified_plus_module(), "CleanTV.minus.denotes");
    let witness = kernel_certified_theorems(&other).expect("valid module");
    let report =
        link_spec_modules_with_theorems(&other, None, Some(&witness), SpecLinkOptions::default())
            .unwrap();
    assert!(
        matches!(
            report.violations.as_slice(),
            [SpecLinkViolation::CleanTheoremUnresolved { theorem, .. }]
                if theorem == "CleanTV.minus.denotes"
        ),
        "{:?}",
        report.violations
    );

    // A genuine certificate whose `theorems` list is PADDED with a name the
    // kernel never checked: the padded name must not reach the witness. The
    // replay refuses the certificate (a listed theorem must be a theorem of
    // the anchor environment whose term passes), so the module does not
    // validate and there is no witness at all — the binding it would have
    // resolved stays unresolved.
    let mut padded = with_clean_theorem_binding(certified_plus_module(), "Ring.push_refines");
    let ProofEvidence::CleanCic { kernel_recheck, .. } = &mut padded.proof_certificates[0].evidence
    else {
        unreachable!("the minter emits CleanCic");
    };
    kernel_recheck
        .as_mut()
        .expect("the minted certificate carries a kernel re-check")
        .theorems
        .push("Ring.push_refines".to_string());
    match kernel_certified_theorems(&padded) {
        Ok(witness) => panic!("a padded theorem list minted a witness: {witness:?}"),
        Err(errors) => assert!(!errors.is_empty()),
    }

    let mut forged = with_clean_theorem_binding(certified_plus_module(), "CleanTV.plus.denotes");
    let ProofEvidence::CleanCic { term, .. } = &mut forged.proof_certificates[0].evidence else {
        unreachable!("the minter emits CleanCic");
    };
    term.clear();
    assert!(kernel_certified_theorems(&forged).is_err());
    let report =
        link_spec_modules_with_theorems(&forged, None, None, SpecLinkOptions::default()).unwrap();
    assert!(!report.is_certifying());
    assert!(
        report.violations.iter().any(|v| matches!(
            v,
            SpecLinkViolation::CleanTheoremUnresolved { detail, .. }
                if detail.contains("no kernel re-check witness was supplied")
        )),
        "{:?}",
        report.violations
    );
}

// ---------------------------------------------------------------------------
// Ported proof-program rows (docs/roadmap: WS4.14 "GAP flips")
// ---------------------------------------------------------------------------

/// `goal-g1-g8/s3-g6-tla-temporal` — a TLA-shaped machine's temporal
/// properties birth TYPED, OWNED Trust-IR obligations: `Conn { Idle, Open,
/// Closed }` with the invariant `state != Closed => fd >= 0`, the liveness
/// `Open ~> Closed` under `WF(close)`, a `TemporalSafety` and a `Liveness`
/// obligation carrying typed bindings over the machine's variables and a
/// backref to the property each discharges. The module validates and its
/// canonical identity sees the carrier; re-pointing one backref at an
/// undeclared property is the refusal twin.
#[test]
fn goal_g1_g8_s3_g6_tla_temporal() {
    let mut m = bump_module();
    let mut conn = SpecModule::design_only("Conn");
    conn.vars = vec![
        SpecVar::new("state", "0..2").with_sort(ClauseSort::Int),
        SpecVar::new("fd", "Int").with_sort(ClauseSort::Int),
    ];
    conn.actions = vec!["open".to_string(), "close".to_string()];
    let fd_valid = formula(
        "(=> (not (= state 2)) (>= fd 0))",
        vec![
            bind("state", ClauseSort::Int, ClausePlace::SpecVar { index: 0 }),
            bind("fd", ClauseSort::Int, ClausePlace::SpecVar { index: 1 }),
        ],
    );
    let is_open = formula(
        "(= state 1)",
        vec![bind(
            "state",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 0 },
        )],
    );
    let is_closed = formula(
        "(= state 2)",
        vec![bind(
            "state",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 0 },
        )],
    );
    let close_relation = formula(
        "(and (= state 1) (= state_next 2))",
        vec![
            bind("state", ClauseSort::Int, ClausePlace::SpecVar { index: 0 }),
            bind(
                "state_next",
                ClauseSort::Int,
                ClausePlace::SpecVarNext { index: 0 },
            ),
        ],
    );
    conn.invariants = vec![
        SpecInvariant::new("FdValid", "(=> (not (= state 2)) (>= fd 0))")
            .with_typed(fd_valid.clone()),
    ];
    conn.temporal = vec![
        SpecTemporal::new("AlwaysFdValid", TemporalForm::Always(fd_valid.clone())),
        SpecTemporal::new(
            "OpenLeadsToClosed",
            TemporalForm::LeadsTo(is_open, is_closed),
        ),
        SpecTemporal::new(
            "CloseFair",
            TemporalForm::WeakFair {
                action: "close".to_string(),
                relation: Some(close_relation),
            },
        ),
    ];
    m.spec_modules.push(conn);
    let mut safety = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::TemporalSafety,
        ProofStatus::Pending,
        "[] FdValid",
    )
    .with_formula(fd_valid);
    safety.spec = Some(SpecObligationRef::new("Conn", "AlwaysFdValid"));
    let mut liveness = ProofObligation::new(
        ProofId::new(1),
        ObligationKind::Liveness,
        ProofStatus::Pending,
        "Open ~> Closed",
    )
    .with_formula(formula(
        "(= state 2)",
        vec![bind(
            "state",
            ClauseSort::Int,
            ClausePlace::SpecVar { index: 0 },
        )],
    ));
    liveness.spec = Some(SpecObligationRef::new("Conn", "OpenLeadsToClosed"));
    m.proof_obligations.push(safety);
    m.proof_obligations.push(liveness);
    assert_clean(&m);
    // (The v46 codec round trip of this shape is pinned by
    // `trust-ir/tests/spec_carrier.rs`; here the canonical identity must at
    // least see the carrier.)
    let mut untyped = m.clone();
    untyped.spec_modules[0].temporal.clear();
    assert_ne!(m.stable_digest(), untyped.stable_digest());

    let mut twin = m.clone();
    twin.proof_obligations[1].spec = Some(SpecObligationRef::new("Conn", "OpenLeadsToIdle"));
    let errors = spec_ref_errors(&twin);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].0, 1);
    assert_eq!(errors[0].2, "OpenLeadsToIdle");
}

/// `spec-surface-0709/33-temporal-spec-modules` — the ratified lane keeps the
/// temporal PROPOSITION in Clean; the format gap was `SpecProof.kind` having
/// no Clean-theorem kind. Now a machine's action binds to a Clean theorem by
/// its kernel name, and the binding is honoured ONLY through the kernel
/// re-check witness: the certified `plus` module's `CleanTV.plus.denotes`
/// resolves; the same name on a module whose certificate was forged does not.
#[test]
fn spec_surface_0709_33_temporal_spec_modules() {
    let m = with_clean_theorem_binding(certified_plus_module(), "CleanTV.plus.denotes");
    assert_eq!(
        m.spec_modules[0].proofs[0].kind.tag(),
        "clean-theorem",
        "the proof-kind vocabulary names the Clean lane"
    );
    assert_clean(&m);
    let witness = kernel_certified_theorems(&m).expect("valid module");
    let report =
        link_spec_modules_with_theorems(&m, None, Some(&witness), SpecLinkOptions::default())
            .unwrap();
    assert!(report.is_certifying(), "{report:?}");

    let mut forged = m;
    forged.proof_obligations[0].status = ProofStatus::Certified;
    let ProofEvidence::CleanCic { term, .. } = &mut forged.proof_certificates[0].evidence else {
        unreachable!("the minter emits CleanCic");
    };
    *term = vec![0xff];
    let theorems = kernel_certified_theorems(&forged);
    assert!(theorems.is_err(), "a forged kernel term mints no witness");
}

/// `trust-ir-self-declared/speccore-serialized-clause-carrier` — the design
/// wanted a zero-dep serialized clause carrier with the meaning re-derived at
/// the consumer. The ratified answer (DG-29) is NOT a second `SpecCore`
/// grammar: the typed invariant IS the shared first-order `ProofFormula`,
/// with its `bindings` naming spec variables, so two producers stating the
/// same clause over the same machine encode byte-identically and a consumer
/// re-derives the binding from the module alone (`SpecVar.sort` + the
/// `SpecVar` place), with no producer-private schema in the loop.
#[test]
fn trust_ir_self_declared_speccore_serialized_clause_carrier() {
    // The carrier's TYPE is the contract clause carrier, not a new language.
    let ring = typed_ring();
    assert_eq!(
        std::any::type_name_of_val(&ring.invariants[0].typed),
        std::any::type_name::<Option<ProofFormula>>()
    );
    // Two independent statements of the same clause — what a Rust producer
    // and a Clean producer each emit — are equal and encode identically.
    let from_rust = {
        let mut m = bump_module();
        m.spec_modules.push(typed_ring());
        m
    };
    let from_clean = {
        let mut m = bump_module();
        let mut ring = SpecModule::design_only("ring");
        ring.vars = vec![SpecVar::new("seq", "0..7").with_sort(ClauseSort::Int)];
        ring.actions = vec!["Push".to_string(), "Pop".to_string()];
        ring.invariants = vec![
            SpecInvariant::new("BoundedSeq", "(<= seq 7)").with_typed(formula(
                "(<= seq 7)",
                vec![bind(
                    "seq",
                    ClauseSort::Int,
                    ClausePlace::SpecVar { index: 0 },
                )],
            )),
        ];
        ring.temporal = vec![
            SpecTemporal::new("AlwaysBounded", TemporalForm::Always(bounded())),
            SpecTemporal::new("EventuallyFull", TemporalForm::Eventually(full())),
        ];
        m.spec_modules.push(ring);
        m
    };
    assert_eq!(from_rust.spec_modules, from_clean.spec_modules);
    assert_eq!(from_rust.stable_digest(), from_clean.stable_digest());
    // The consumer re-derives what each free name denotes from the module
    // alone: the binding's place indexes `vars`, whose declared sort agrees.
    let typed = from_rust.spec_modules[0].invariants[0]
        .typed
        .as_ref()
        .unwrap();
    for (name, binding) in &typed.bindings {
        let ClausePlace::SpecVar { index } = binding.place else {
            panic!("{name} is not a spec-variable place");
        };
        let var = &from_rust.spec_modules[0].vars[index as usize];
        assert_eq!(var.name, *name);
        assert_eq!(var.sort, Some(binding.sort.clone()));
    }
    assert_clean(&from_rust);
    // And the mode is the guard: the same machine `Linked` is read (S3) — the
    // typed carrier does not replace the surface text, it binds it.
    let mut linked = from_rust;
    linked.spec_modules[0].enforcement = SpecEnforcementMode::Linked;
    linked.spec_modules[0].waivers = vec![
        SpecWaiver {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            reason: "probe".to_string(),
        },
        SpecWaiver {
            machine: "ring".to_string(),
            action: "Pop".to_string(),
            reason: "probe".to_string(),
        },
    ];
    assert_clean(&linked);
}

// ---------------------------------------------------------------------------
// Adversarial review (WS4.14).
// ---------------------------------------------------------------------------

/// ADVERSARIAL — a temporal obligation whose binding SPELLS a different state
/// variable of the machine it discharges a property of.
///
/// The binding is what resolves the name, so `(not seq)` "means" variable 1.
/// But every reader that puts the formula's text beside the machine's `vars`
/// — the S3 agreement check inside the machine does exactly that — reads
/// `seq` as variable 0, an `Int`. One name, two readings, so it is refused
/// here exactly as it is inside the machine's own carriers.
#[test]
fn an_obligation_binding_may_not_spell_a_different_state_variable() {
    let mut m = bump_module();
    let mut ring = typed_ring();
    ring.vars
        .push(SpecVar::new("empty", "Bool").with_sort(ClauseSort::Bool));
    m.spec_modules.push(ring);
    let mut shadowed = ProofFormula::smtlib2("(not seq)", "Bool");
    shadowed.bindings = vec![bind(
        "seq",
        ClauseSort::Bool,
        ClausePlace::SpecVar { index: 1 },
    )];
    let mut o = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::TemporalSafety,
        ProofStatus::Pending,
        "the ring stays bounded",
    )
    .with_formula(shadowed);
    o.spec = Some(SpecObligationRef::new("ring", "AlwaysBounded"));
    m.proof_obligations.push(o);

    let errors = validate_module(&m);
    let hits: Vec<_> = errors
        .iter()
        .filter(|e| matches!(e, ValidationError::InvalidObligationBinding { .. }))
        .collect();
    assert_eq!(hits.len(), 1, "{errors:?}");
    let rendered = hits[0].to_string();
    assert!(
        rendered.contains("is the name of state variable 1")
            || rendered.contains("is the name of state variable 0"),
        "{rendered}"
    );

    // Mutation control: the SAME shape with the name that variable 1 really
    // carries is the honest spelling and validates.
    let mut honest = ProofFormula::smtlib2("(not empty)", "Bool");
    honest.bindings = vec![bind(
        "empty",
        ClauseSort::Bool,
        ClausePlace::SpecVar { index: 1 },
    )];
    m.proof_obligations[0].formula = Some(honest);
    assert!(
        !validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidObligationBinding { .. })),
        "the honest binding must not be refused"
    );
}
