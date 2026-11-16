// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Inst::BoxDeref` (wire v74, `docs/SPEC_RATIFICATIONS.md` §28): the carried
//! validity fact is judged by the validator, transported by every format and
//! never read by the reference interpreter, which decides the conjuncts it
//! can from the pointer itself.
//!
//! The must-refuse corpus pins one verdict per rule on committed artifacts
//! (`refuse/box_deref_*`). These tests cover what a corpus row cannot: that
//! each rule is reached by a mutation of an ACCEPTED module (so the accepted
//! module is the control of every refusal here), the interpreter's undefined
//! behaviour, and the text, binary and merge transports.

use trust_ir::box_validity::{
    BoxDerefSite, BoxFactSession, BoxValidityFact, BoxValidityNonClaim, BoxValidityTier,
    ConjunctEvidence, JudgedBody, PremiseRoot, ProducingSession, StandingAssumption,
    ValidityConjunct, ValidityEvidence,
};
use trust_ir::constant::Constant;
use trust_ir::inst::{AllocOrigin, AssertKind, BinOp, CastOp, ICmpOp, Inst};
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{
    BodyGate, EffectPlace, EffectSet, EffectSummary, Endianness, FunctionSummary, Module,
    TargetInfo, Ty,
};
use trust_ir_build::{
    CodegenAdmission, ModuleBuilder, ValidationError, validate_module,
    validate_module_for_codegen_with,
};

fn site(ordinal: u32) -> BoxDerefSite {
    BoxDerefSite {
        item: [0xab; 16],
        ordinal,
    }
}

fn premise(ordinal: u32, root: PremiseRoot) -> BoxValidityFact {
    BoxValidityFact::premise(site(ordinal), BoxFactSession::PROOF_SNAPSHOT, root)
}

/// A 32-bit little-endian target: pointers and `usize` are four bytes.
fn wasm32() -> TargetInfo {
    TargetInfo {
        triple: "wasm32-unknown-unknown".into(),
        pointer_size: 4,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn builder(name: &str, target: Option<TargetInfo>) -> ModuleBuilder {
    match target {
        Some(target) => ModuleBuilder::new_with_target_info(name, target),
        None => ModuleBuilder::new(name),
    }
}

/// `fn unbox(p: ptr) -> i64`: the deref of the parameter under `fact`, then
/// a load through the result.
fn premised_module(fact: BoxValidityFact) -> Module {
    premised_module_on(None, Ty::I64, fact)
}

/// [`premised_module`] over `pointee` on `target`.
fn premised_module_on(target: Option<TargetInfo>, pointee: Ty, fact: BoxValidityFact) -> Module {
    let mut mb = builder("box_deref_premised", target);
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![pointee.clone()]);
    let mut fb = mb.function("unbox", ft);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let boxed = fb.box_deref(pointee.clone(), pointer, fact);
    let read = fb.load(pointee, boxed);
    fb.ret(vec![read]);
    fb.set_body_gate(BodyGate::Ungated);
    fb.build();
    mb.build().expect("the premised module builds")
}

/// A module in which every root has its anchor: `make() -> ptr` allocates,
/// and `unbox(p: ptr) -> i64` holds a parameter, a call of `make` and an
/// allocation of its own, then derefs the one of them `root` names.
fn rooted_module(root: PremiseRoot) -> Module {
    let mut mb = ModuleBuilder::new("box_deref_rooted");
    let make_ty = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let make = {
        let mut fb = mb.function("make", make_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let raw = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
        fb.ret(vec![raw]);
        fb.set_body_gate(BodyGate::Ungated);
        fb.build()
    };
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
    let mut fb = mb.function("unbox", ft);
    let entry = fb.create_block();
    let parameter = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let returned = fb.call(make, vec![]);
    let allocated = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
    let operand = match root {
        PremiseRoot::ParamByValue | PremiseRoot::ReferenceArgBoxValid => parameter,
        PremiseRoot::AllocPostcondition => allocated,
        PremiseRoot::ReturnedBoxDischarged | PremiseRoot::ReturnedBoxAssumed => returned,
    };
    let boxed = fb.box_deref(Ty::I64, operand, premise(0, root));
    fb.ret(vec![boxed]);
    fb.set_body_gate(BodyGate::Ungated);
    fb.build();
    mb.build().expect("the rooted module builds")
}

/// `fn subject(<p: ptr>) -> ptr`: an optional parameter, an optional fresh
/// allocation, the operand `shape` builds from them, its deref premised on
/// `root`, and the result returned.
fn premise_subject(
    with_parameter: bool,
    with_allocation: bool,
    root: PremiseRoot,
    shape: fn(
        &mut trust_ir_build::FunctionBuilder<'_>,
        Option<trust_ir::ValueId>,
        Option<trust_ir::ValueId>,
    ) -> trust_ir::ValueId,
) -> Module {
    let mut mb = ModuleBuilder::new("box_deref_premise_subject");
    let params = if with_parameter {
        vec![Ty::Ptr]
    } else {
        vec![]
    };
    let ft = mb.add_func_type(params, vec![Ty::Ptr]);
    let mut fb = mb.function("subject", ft);
    let entry = fb.create_block();
    let parameter = with_parameter.then(|| fb.add_block_param(entry, Ty::Ptr));
    fb.switch_to_block(entry);
    let raw = with_allocation.then(|| fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap));
    let operand = shape(&mut fb, parameter, raw);
    let boxed = fb.box_deref(Ty::I64, operand, premise(0, root));
    fb.ret(vec![boxed]);
    fb.set_body_gate(BodyGate::Ungated);
    fb.build();
    mb.build().expect("the premise subject builds")
}

/// The null and alignment asserts over `checked`, ten instructions:
/// `ptrtoint`, `const 0`, `icmp ne`, the null assert, `const align`,
/// `const align-1`, `and`, `const 0`, `icmp eq`, the alignment assert.
fn result_checks(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    checked: trust_ir::ValueId,
    align: i128,
) {
    let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, checked);
    let zero = fb.const_value(Ty::Usize, Constant::Int(0));
    let nonnull = fb.icmp(ICmpOp::Ne, Ty::Usize, address, zero);
    fb.assert_kind(nonnull, AssertKind::NullPtr);
    let required = fb.const_value(Ty::Usize, Constant::Int(align));
    let mask = fb.const_value(Ty::Usize, Constant::Int(align - 1));
    let low = fb.binop(BinOp::And, Ty::Usize, address, mask);
    let none = fb.const_value(Ty::Usize, Constant::Int(0));
    let aligned = fb.icmp(ICmpOp::Eq, Ty::Usize, low, none);
    fb.assert_kind(
        aligned,
        AssertKind::MisalignedPtr {
            required,
            found: address,
        },
    );
}

/// A fact offering both reserved check entries: `NonNull` and `Aligned` as
/// dominating checks, `Dereferenceable` premised on the parameter.
fn checked_fact() -> BoxValidityFact {
    let mut fact = premise(0, PremiseRoot::ParamByValue);
    fact.evidence[0].evidence = ValidityEvidence::DominatingCheck { align: None };
    fact.evidence[1].evidence = ValidityEvidence::DominatingCheck { align: Some(8) };
    fact
}

/// `fn unbox(p: ptr) -> i64`: the deref under `fact`, the null and alignment
/// asserts over its RESULT, then a load through the result.
fn checked_module(fact: BoxValidityFact) -> Module {
    let mut mb = ModuleBuilder::new("box_deref_checked");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("unbox", ft);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let boxed = fb.box_deref(Ty::I64, pointer, fact);
    result_checks(&mut fb, boxed, 8);
    let read = fb.load(Ty::I64, boxed);
    fb.ret(vec![read]);
    fb.set_body_gate(BodyGate::Ungated);
    fb.build();
    mb.build().expect("the checked module builds")
}

fn fact_of(module: &mut Module) -> &mut BoxValidityFact {
    module.functions[0].blocks[0]
        .body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            Inst::BoxDeref { fact, .. } => Some(&mut **fact),
            _ => None,
        })
        .expect("the module's Box deref")
}

/// The names of the errors `validate_module` reports, deduplicated in order.
fn refusals(module: &Module) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    for error in validate_module(module) {
        let text = format!("{error:?}");
        let name = text
            .split(|c: char| !c.is_alphanumeric())
            .next()
            .unwrap_or_default()
            .to_string();
        if !names.contains(&name) {
            names.push(name);
        }
    }
    names
}

/// The accept path: a premise on each pinned root is accepted in a function
/// that holds the root's anchor, with every conjunct on that one root.
#[test]
fn a_premise_on_every_root_is_accepted_where_the_function_has_its_anchor() {
    for root in PremiseRoot::ALL {
        let module = rooted_module(root);
        assert_eq!(validate_module(&module), vec![], "{root:?}");
        let fact = module.functions[1].blocks[0]
            .body
            .iter()
            .find_map(|node| match &node.inst {
                Inst::BoxDeref { fact, .. } => Some(fact),
                _ => None,
            })
            .expect("the rooted module's Box deref");
        assert_eq!(fact.premise_root(), Some(root));
        assert_eq!(fact.weakest_tier(), Some(root.tier()));
    }
    assert_eq!(
        validate_module(&premised_module(premise(0, PremiseRoot::ParamByValue))),
        vec![]
    );
}

/// A Box deref checks point-in-time allocation validity. Section 28 licenses
/// no deletion or movement of that check: DCE retains it, function attributes
/// cannot summarize it as readnone/readonly, and an effect summary must name
/// the operand's pointee as read.
#[test]
fn box_deref_is_non_dce_and_memory_dependent_at_its_program_point() {
    let control = premise_subject(
        true,
        false,
        PremiseRoot::ParamByValue,
        |_fb, parameter, _raw| parameter.expect("the control has its parameter"),
    );
    let box_deref = control.functions[0].blocks[0]
        .body
        .iter()
        .find_map(|node| matches!(&node.inst, Inst::BoxDeref { .. }).then_some(&node.inst))
        .expect("the rooted module's Box deref");
    assert!(box_deref.has_observable_effects());
    assert!(box_deref.has_side_effects());
    assert!(!box_deref.is_removable_if_unused());

    for (readonly, readnone, attr) in [(false, true, "readnone"), (true, false, "readonly")] {
        let mut module = control.clone();
        module.functions[0].attrs.readonly = readonly;
        module.functions[0].attrs.readnone = readnone;
        let errors = validate_module(&module);
        assert!(
            errors.iter().any(|error| matches!(
                error,
                ValidationError::FuncAttrClaimViolated {
                    function,
                    attr: claimed,
                    inst,
                    ..
                } if function == "subject" && *claimed == attr && inst.starts_with("box_deref")
            )),
            "{attr}: {errors:?}"
        );
    }

    let mut pure = control.clone();
    pure.functions[0].summary = Some(FunctionSummary::new().with_effects(EffectSummary::pure()));
    let errors = validate_module(&pure);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            ValidationError::EffectSummaryViolated {
                function,
                effect: "reads",
                inst,
                ..
            } if function == "subject" && inst.starts_with("box_deref")
        )),
        "pure summary hid Box validity: {errors:?}"
    );

    let mut declared = control;
    declared.functions[0].summary = Some(FunctionSummary::new().with_effects(
        EffectSummary::pure().reading(EffectSet::of([EffectPlace::ParamPointee { index: 0 }])),
    ));
    assert_eq!(validate_module(&declared), vec![]);
}

#[test]
fn every_single_mutation_of_an_accepted_fact_is_refused_by_its_own_rule() {
    let control = premised_module(premise(0, PremiseRoot::ParamByValue));
    assert_eq!(validate_module(&control), vec![]);
    type Mutation = (&'static str, fn(&mut BoxValidityFact), &'static str);
    let mutations: &[Mutation] = &[
        (
            "drop a conjunct",
            |fact| {
                fact.evidence.remove(1);
            },
            "BoxDerefConjunctCover",
        ),
        (
            "repeat a conjunct",
            |fact| {
                let again = fact.evidence[2].clone();
                fact.evidence.push(again);
            },
            "BoxDerefConjunctCover",
        ),
        (
            "reverse the conjuncts",
            |fact| fact.evidence.reverse(),
            "BoxDerefConjunctCover",
        ),
        (
            "empty the evidence",
            |fact| fact.evidence.clear(),
            "BoxDerefConjunctCover",
        ),
        (
            "add the wide-only conjunct",
            |fact| {
                fact.evidence.push(ConjunctEvidence {
                    conjunct: ValidityConjunct::MetadataValid,
                    evidence: ValidityEvidence::Premise {
                        root: PremiseRoot::ParamByValue,
                        standing: StandingAssumption::PINNED.to_vec(),
                    },
                });
            },
            "BoxDerefConjunctCover",
        ),
        (
            "empty the standing assumptions",
            |fact| {
                if let ValidityEvidence::Premise { standing, .. } = &mut fact.evidence[2].evidence {
                    standing.clear();
                }
            },
            "BoxDerefPremiseNotPinned",
        ),
        (
            "reorder the standing assumptions",
            |fact| {
                if let ValidityEvidence::Premise { standing, .. } = &mut fact.evidence[2].evidence {
                    standing.swap(0, 2);
                }
            },
            "BoxDerefPremiseNotPinned",
        ),
        (
            "judge on the fallback body",
            |fact| fact.session.judged = JudgedBody::OptimizedFallback,
            "BoxDerefSessionRefused",
        ),
        (
            "state a session whose verifier did not run",
            |fact| fact.session.producing = ProducingSession::NonProofSession,
            "BoxDerefSessionRefused",
        ),
        (
            "offer a check for non-nullness",
            |fact| {
                fact.evidence[0].evidence = ValidityEvidence::DominatingCheck { align: None };
            },
            "BoxDerefDominatingCheckInvalid",
        ),
        (
            "offer a check for alignment",
            |fact| {
                fact.evidence[1].evidence = ValidityEvidence::DominatingCheck { align: Some(8) };
            },
            "BoxDerefDominatingCheckInvalid",
        ),
        (
            "offer a check for dereferenceability",
            |fact| {
                fact.evidence[2].evidence = ValidityEvidence::DominatingCheck { align: None };
            },
            "BoxDerefDominatingCheckInvalid",
        ),
        (
            "cite an obligation",
            |fact| {
                fact.evidence[2].evidence = ValidityEvidence::Obligation {
                    obligation: ProofId::new(7),
                };
            },
            "BoxDerefObligationUnbound",
        ),
        (
            "premise one conjunct on another root",
            |fact| {
                if let ValidityEvidence::Premise { root, .. } = &mut fact.evidence[2].evidence {
                    *root = PremiseRoot::ReferenceArgBoxValid;
                }
            },
            "BoxDerefPremiseContradicted",
        ),
        (
            "drop a non-claim",
            |fact| {
                fact.not_claimed.remove(0);
            },
            "BoxDerefNonClaimsNotPinned",
        ),
        (
            "reorder the non-claims",
            |fact| fact.not_claimed.swap(0, 1),
            "BoxDerefNonClaimsNotPinned",
        ),
        (
            "repeat a non-claim",
            |fact| fact.not_claimed.push(BoxValidityNonClaim::Allocator),
            "BoxDerefNonClaimsNotPinned",
        ),
    ];
    for (what, mutate, expected) in mutations {
        let mut module = control.clone();
        mutate(fact_of(&mut module));
        assert_eq!(refusals(&module), vec![expected.to_string()], "{what}");
    }
    // The session rule is about the session alone: outside a proof session
    // no root is admitted.
    for root in PremiseRoot::ALL {
        let mut module = rooted_module(root);
        for node in &mut module.functions[1].blocks[0].body {
            if let Inst::BoxDeref { fact, .. } = &mut node.inst {
                fact.session.producing = ProducingSession::NonProofSession;
            }
        }
        assert_eq!(
            refusals(&module),
            vec!["BoxDerefSessionRefused".to_string()],
            "{root:?}"
        );
    }
    let mut module = control.clone();
    fact_of(&mut module).session.producing = ProducingSession::NonProofSession;
    fact_of(&mut module).session.judged = JudgedBody::OptimizedFallback;
    assert_eq!(
        validate_module(&module)
            .iter()
            .filter(|error| matches!(error, ValidationError::BoxDerefSessionRefused { .. }))
            .count(),
        2,
        "each false half of the session condition is reported"
    );
}

/// Dominating-check evidence is refused in EVERY shape, the shapes an
/// earlier draft accepted included: asserts over the result that dominate
/// the load, and the null check with a size conjunct. One refusal per
/// offered entry, and no other error.
#[test]
fn no_dominating_check_is_admitted_in_any_shape() {
    let checked = checked_module(checked_fact());
    let errors = validate_module(&checked);
    assert_eq!(errors.len(), 2, "{errors:?}");
    for (error, expected) in errors.iter().zip(["nonnull", "aligned"]) {
        assert!(
            matches!(
                error,
                ValidationError::BoxDerefDominatingCheckInvalid { conjunct, .. }
                    if *conjunct == expected
            ),
            "{error:?}"
        );
    }

    // The null check with the zero-size exemption, stating the pointee's
    // own size.
    let mut mb = ModuleBuilder::new("box_deref_null_check_with_size");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
    let mut fb = mb.function("unbox", ft);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let mut fact = premise(0, PremiseRoot::ParamByValue);
    fact.evidence[0].evidence = ValidityEvidence::DominatingCheck { align: None };
    let boxed = fb.box_deref(Ty::I64, pointer, fact);
    let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, boxed);
    let zero = fb.const_value(Ty::Usize, Constant::Int(0));
    let is_null = fb.icmp(ICmpOp::Eq, Ty::Usize, address, zero);
    let size = fb.const_value(Ty::Usize, Constant::Int(8));
    let none = fb.const_value(Ty::Usize, Constant::Int(0));
    let is_sized = fb.icmp(ICmpOp::Ne, Ty::Usize, size, none);
    let both = fb.binop(BinOp::BAnd, Ty::Bool, is_null, is_sized);
    let yes = fb.const_value(Ty::Bool, Constant::Bool(true));
    let ok = fb.binop(BinOp::BXor, Ty::Bool, both, yes);
    fb.assert_kind(ok, AssertKind::NullPtr);
    fb.ret(vec![boxed]);
    fb.set_body_gate(BodyGate::Ungated);
    fb.build();
    let module = mb.build().expect("the null-check module builds");
    assert_eq!(
        refusals(&module),
        vec!["BoxDerefDominatingCheckInvalid".to_string()]
    );
}

/// Two shapes a rule that exempted `ptrtoint` of the result from "the uses
/// a check must dominate" would have accepted with the address dereferenced
/// unchecked: the address round-tripped through `inttoptr` and loaded before
/// the assert, and an assert in a block the load's path never enters.
#[test]
fn an_address_that_escapes_through_ptrtoint_is_never_a_checked_pointer() {
    for assert_in_sibling_block in [false, true] {
        let mut mb = ModuleBuilder::new("box_deref_address_round_trip");
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::Bool], vec![Ty::I64]);
        let mut fb = mb.function("round_trip", ft);
        let entry = fb.create_block();
        let pointer = fb.add_block_param(entry, Ty::Ptr);
        let choose = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        let mut fact = premise(0, PremiseRoot::ParamByValue);
        fact.evidence[0].evidence = ValidityEvidence::DominatingCheck { align: None };
        let boxed = fb.box_deref(Ty::I64, pointer, fact);
        let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, boxed);
        let again = fb.cast(CastOp::IntToPtr, Ty::Usize, Ty::Ptr, address);
        let zero = fb.const_value(Ty::Usize, Constant::Int(0));
        let nonnull = fb.icmp(ICmpOp::Ne, Ty::Usize, address, zero);
        if assert_in_sibling_block {
            let checking = fb.create_block();
            let reading = fb.create_block();
            fb.condbr(choose, checking, vec![], reading, vec![]);
            fb.switch_to_block(checking);
            fb.assert_kind(nonnull, AssertKind::NullPtr);
            let seven = fb.const_value(Ty::I64, Constant::Int(7));
            fb.ret(vec![seven]);
            fb.switch_to_block(reading);
            let read = fb.load(Ty::I64, again);
            fb.ret(vec![read]);
        } else {
            let read = fb.load(Ty::I64, again);
            fb.assert_kind(nonnull, AssertKind::NullPtr);
            fb.ret(vec![read]);
        }
        fb.set_body_gate(BodyGate::Ungated);
        fb.build();
        let module = mb.build().expect("the round-trip module builds");
        assert_eq!(
            refusals(&module),
            vec!["BoxDerefDominatingCheckInvalid".to_string()],
            "assert_in_sibling_block={assert_in_sibling_block}"
        );
    }
}

/// Obligation evidence is refused whatever the cited row is: absent, of
/// another kind, owned by another function, sited elsewhere, or a
/// `MemorySafety` row owned by the function and sited on the instruction.
/// The last is the case the refusal exists for: nothing compares its formula
/// with the conjunct.
#[test]
fn no_obligation_is_admitted_however_it_is_bound() {
    use trust_ir::proof::{ObligationKind, ObligationSite, ProofObligation, ProofStatus};
    type Rebind = fn(&mut ProofObligation, &Module);
    let rebinds: &[(&str, Option<Rebind>)] = &[
        ("no such row", None),
        ("bound by kind, owner and site", Some(|_, _| {})),
        (
            "another kind",
            Some(|row, _| row.kind = ObligationKind::Ownership),
        ),
        (
            "another owner",
            Some(|row, _| row.function = Some(FuncId::new(9))),
        ),
        (
            "another site",
            Some(|row, module| {
                let function = &module.functions[0];
                row.site = Some(ObligationSite::new(function.id, function.blocks[0].id, 1));
            }),
        ),
    ];
    for (what, rebind) in rebinds {
        let mut module = premised_module(premise(0, PremiseRoot::ParamByValue));
        if let Some(rebind) = rebind {
            let function = &module.functions[0];
            let mut row = ProofObligation::new(
                ProofId::new(0),
                ObligationKind::MemorySafety,
                ProofStatus::Pending,
                "true",
            )
            .with_function(function.id)
            .with_site(ObligationSite::new(function.id, function.blocks[0].id, 0));
            rebind(&mut row, &module);
            module.proof_obligations.push(row);
        }
        // One row cited for all three conjuncts: no root, no standing
        // assumption, three refusals.
        for entry in &mut fact_of(&mut module).evidence {
            entry.evidence = ValidityEvidence::Obligation {
                obligation: ProofId::new(0),
            };
        }
        let unbound = validate_module(&module)
            .into_iter()
            .filter(|error| matches!(error, ValidationError::BoxDerefObligationUnbound { .. }))
            .count();
        assert_eq!(unbound, 3, "{what}");
    }
}

/// Rule 9: a premise the function itself contradicts is refused. Each case
/// is one mutation away from an accepted module, and yields that rule alone.
#[test]
fn a_premise_the_function_contradicts_is_refused() {
    type Shape = fn(
        &mut trust_ir_build::FunctionBuilder<'_>,
        Option<trust_ir::ValueId>,
        Option<trust_ir::ValueId>,
    ) -> trust_ir::ValueId;
    let parameter: Shape = |_, parameter, _| parameter.expect("a parameter");
    let allocation: Shape = |_, _, raw| raw.expect("an allocation");

    // Controls: each root with its anchor.
    for (with_parameter, with_allocation, root, shape) in [
        (true, false, PremiseRoot::ParamByValue, parameter),
        (true, false, PremiseRoot::ReferenceArgBoxValid, parameter),
        (false, true, PremiseRoot::AllocPostcondition, allocation),
    ] {
        assert_eq!(
            validate_module(&premise_subject(
                with_parameter,
                with_allocation,
                root,
                shape
            )),
            vec![],
            "{root:?}"
        );
    }

    let contradicted: [(&str, bool, bool, PremiseRoot, Shape); 9] = [
        (
            "a null operand",
            false,
            true,
            PremiseRoot::AllocPostcondition,
            |fb, _, _| fb.null_ptr(),
        ),
        (
            "an undef operand",
            false,
            true,
            PremiseRoot::AllocPostcondition,
            |fb, _, _| fb.undef(Ty::Ptr),
        ),
        (
            "an operand made from an integer",
            true,
            false,
            PremiseRoot::ParamByValue,
            |fb, _, _| {
                let address = fb.const_value(Ty::Usize, Constant::Int(4096));
                fb.cast(CastOp::IntToPtr, Ty::Usize, Ty::Ptr, address)
            },
        ),
        (
            "a parameter root without a parameter",
            false,
            true,
            PremiseRoot::ParamByValue,
            allocation,
        ),
        (
            "a reference-argument root without a parameter",
            false,
            true,
            PremiseRoot::ReferenceArgBoxValid,
            allocation,
        ),
        (
            "an allocation root without an allocation or a call",
            true,
            false,
            PremiseRoot::AllocPostcondition,
            parameter,
        ),
        (
            "a discharged returned-box root without a call",
            true,
            true,
            PremiseRoot::ReturnedBoxDischarged,
            parameter,
        ),
        (
            "an assumed returned-box root without a call",
            true,
            true,
            PremiseRoot::ReturnedBoxAssumed,
            parameter,
        ),
        (
            "a freed operand",
            false,
            true,
            PremiseRoot::AllocPostcondition,
            |fb, _, raw| {
                let raw = raw.expect("an allocation");
                fb.dealloc(raw);
                raw
            },
        ),
    ];
    for (what, with_parameter, with_allocation, root, shape) in contradicted {
        let module = premise_subject(with_parameter, with_allocation, root, shape);
        let errors = validate_module(&module);
        assert_eq!(errors.len(), 1, "{what}: {errors:?}");
        assert!(
            matches!(
                errors[0],
                ValidationError::BoxDerefPremiseContradicted { .. }
            ),
            "{what}: {errors:?}"
        );
    }
}

/// The boundary of rule 9, pinned so it is not read as more than it is: a
/// `Dealloc` on ONE path to the deref does not dominate it, and the rule
/// does not refuse. The premise is then false on that path and the module
/// still validates; the interpreter reports the undefined behaviour.
#[test]
fn the_sanity_rule_decides_dominance_only() {
    let mut mb = ModuleBuilder::new("box_deref_freed_on_one_path");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::I64]);
    let mut fb = mb.function("run", ft);
    let entry = fb.create_block();
    let freeing = fb.create_block();
    let join = fb.create_block();
    let choose = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    let raw = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
    fb.condbr(choose, freeing, vec![], join, vec![]);
    fb.switch_to_block(freeing);
    fb.dealloc(raw);
    fb.br(join, vec![]);
    fb.switch_to_block(join);
    let _boxed = fb.box_deref(Ty::I64, raw, premise(0, PremiseRoot::AllocPostcondition));
    let nine = fb.const_value(Ty::I64, Constant::Int(9));
    fb.ret(vec![nine]);
    fb.set_body_gate(BodyGate::Ungated);
    fb.build();
    let module = mb.build().expect("the one-path module builds");
    assert_eq!(validate_module(&module), vec![]);
    let run = |freed: bool| {
        trust_ir::interpret::Interpreter::with_module(&module)
            .execute_func(
                FuncId::new(0),
                [trust_ir::interpret::InterpretValue::bool(freed)],
            )
            .map(|outcome| outcome.returns[0].as_int().unwrap().as_signed())
            .map_err(|error| format!("{error:?}"))
    };
    assert_eq!(run(false), Ok(9));
    let error = run(true).expect_err("the freed path");
    assert!(error.contains("Dereferenceable is false"), "{error}");
}

#[test]
fn the_evidence_floor_refuses_by_tier_and_never_relaxes_a_rule() {
    let floor_errors = |module: &Module, floor| {
        let admission = CodegenAdmission::pinned().with_require_box_validity_evidence(floor);
        validate_module_for_codegen_with(module, &admission)
            .into_iter()
            .filter(|error| matches!(error, ValidationError::BoxValidityEvidenceBelowFloor { .. }))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        CodegenAdmission::pinned().require_box_validity_evidence(),
        None
    );
    // Every root, under every floor: refused exactly when the root's class
    // is below the floor, once per conjunct, naming the class.
    for root in PremiseRoot::ALL {
        let module = rooted_module(root);
        assert_eq!(floor_errors(&module, None), vec![], "{root:?}");
        for floor in BoxValidityTier::ALL {
            let below = floor_errors(&module, Some(floor));
            if root.tier() >= floor {
                assert_eq!(below, vec![], "{root:?} under {floor:?}");
                continue;
            }
            assert_eq!(below.len(), 3, "{root:?} under {floor:?}: {below:?}");
            for error in &below {
                assert!(
                    matches!(
                        error,
                        ValidationError::BoxValidityEvidenceBelowFloor { tier, floor: stated, .. }
                            if *tier == root.tier().name() && *stated == floor.name()
                    ),
                    "{error:?}"
                );
            }
        }
    }
    // The split is real: a floor at the named-premise class admits the
    // roots a session verified something behind and refuses the two it
    // verified nothing behind.
    let admitted: Vec<PremiseRoot> = PremiseRoot::ALL
        .into_iter()
        .filter(|root| {
            floor_errors(&rooted_module(*root), Some(BoxValidityTier::NamedPremise)).is_empty()
        })
        .collect();
    assert_eq!(
        admitted,
        [
            PremiseRoot::ParamByValue,
            PremiseRoot::AllocPostcondition,
            PremiseRoot::ReturnedBoxDischarged
        ]
    );
    // `NotAdmitted` is the ordered minimum and therefore a no-op floor.
    // Reserved evidence stays refused by structural rules 6 and 7; every
    // meaningful floor above the minimum also places it below the floor.
    let checked = checked_module(checked_fact());
    let below = floor_errors(&checked, Some(BoxValidityTier::NotAdmitted));
    assert_eq!(below, vec![]);
    let below = floor_errors(&checked, Some(BoxValidityTier::AssumedRootPremise));
    assert_eq!(below.len(), 2, "{below:?}");

    // A malformed fact is refused with no floor set and with the lowest one.
    let mut malformed = premised_module(premise(0, PremiseRoot::ParamByValue));
    fact_of(&mut malformed).evidence.pop();
    for floor in [None, Some(BoxValidityTier::NotAdmitted)] {
        let admission = CodegenAdmission::pinned().with_require_box_validity_evidence(floor);
        assert!(
            validate_module_for_codegen_with(&malformed, &admission)
                .iter()
                .any(|error| matches!(error, ValidationError::BoxDerefConjunctCover { .. })),
            "{floor:?}"
        );
    }
}

/// `fn run() -> i64`: allocate `allocated`, store 9, transform the pointer
/// with `shape`, deref it as a Box of `pointee`, and return 9.
fn executing_module(
    allocated: Ty,
    pointee: Ty,
    shape: fn(&mut trust_ir_build::FunctionBuilder<'_>, trust_ir::ValueId) -> trust_ir::ValueId,
) -> Module {
    executing_module_on(None, allocated, pointee, shape)
}

/// [`executing_module`] on `target`.
fn executing_module_on(
    target: Option<TargetInfo>,
    allocated: Ty,
    pointee: Ty,
    shape: fn(&mut trust_ir_build::FunctionBuilder<'_>, trust_ir::ValueId) -> trust_ir::ValueId,
) -> Module {
    let mut mb = builder("box_deref_executes", target);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("run", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let raw = fb.heap_alloc(allocated, None, None, AllocOrigin::RustHeap);
    let pointer = shape(&mut fb, raw);
    let _boxed = fb.box_deref(
        pointee,
        pointer,
        premise(0, PremiseRoot::AllocPostcondition),
    );
    let nine = fb.const_value(Ty::I64, Constant::Int(9));
    fb.ret(vec![nine]);
    fb.set_body_gate(BodyGate::Ungated);
    fb.build();
    mb.build().expect("the executing module builds")
}

fn run(module: &Module) -> Result<i128, String> {
    trust_ir::interpret::Interpreter::with_module(module)
        .execute_func(FuncId::new(0), [])
        .map(|outcome| outcome.returns[0].as_int().unwrap().as_signed())
        .map_err(|error| format!("{error:?}"))
}

#[test]
fn the_interpreter_is_the_identity_on_a_valid_box_pointer() {
    let module = executing_module(Ty::I64, Ty::I64, |_, raw| raw);
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(run(&module), Ok(9));
}

#[test]
fn a_false_conjunct_is_undefined_behaviour_where_the_interpreter_can_decide_it() {
    // NonNull.
    let null = executing_module(Ty::I64, Ty::I64, |fb, _| fb.null_ptr());
    let error = run(&null).expect_err("a null Box pointer");
    assert!(error.contains("NonNull is false"), "{error}");

    // Aligned: one byte into an 8-aligned allocation.
    let misaligned = executing_module(Ty::I64, Ty::I64, |fb, raw| {
        let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, raw);
        let one = fb.const_value(Ty::Usize, Constant::Int(1));
        let moved = fb.binop(BinOp::Add, Ty::Usize, address, one);
        fb.cast(CastOp::IntToPtr, Ty::Usize, Ty::Ptr, moved)
    });
    let error = run(&misaligned).expect_err("a misaligned Box pointer");
    assert!(error.contains("Aligned is false"), "{error}");

    // Dereferenceable: an aligned address with no allocation behind it.
    let dangling = executing_module(Ty::I64, Ty::I64, |fb, _| {
        let address = fb.const_value(Ty::Usize, Constant::Int(4096));
        fb.cast(CastOp::IntToPtr, Ty::Usize, Ty::Ptr, address)
    });
    let error = run(&dangling).expect_err("a dangling Box pointer");
    assert!(error.contains("Dereferenceable is false"), "{error}");

    // Dereferenceable: the allocation is smaller than the pointee. A stack
    // allocation has exact bounds in the memory model; a heap allocation
    // carries the allocator's readable usable-size slack, which counts as
    // part of its extent.
    let short = executing_module(Ty::I64, Ty::I64, |fb, _| fb.alloca_aligned(Ty::I32, 8));
    let error = run(&short).expect_err("an allocation smaller than the pointee");
    assert!(
        error.contains("BoxDeref: Dereferenceable is false"),
        "{error}"
    );

    // Dereferenceable: the allocation was freed. The address is unchanged
    // (non-null, aligned), so only the point-in-time conjunct is false.
    let freed = executing_module(Ty::I64, Ty::I64, |fb, raw| {
        fb.dealloc(raw);
        raw
    });
    let error = run(&freed).expect_err("a freed Box pointer");
    assert!(
        error.contains("BoxDeref: Dereferenceable is false"),
        "{error}"
    );
    assert!(!error.contains("NonNull"), "{error}");
    assert!(!error.contains("Aligned"), "{error}");
}

/// `fn run() -> i64`: store 9 through a fresh allocation, deref the pointer
/// as a Box, and return what a load through the RESULT reads plus whether
/// the result's address equals the operand's.
#[test]
fn the_result_is_the_operand_in_bits_and_provenance() {
    let mut mb = ModuleBuilder::new("box_deref_identity");
    let ft = mb.add_func_type(vec![], vec![Ty::I64, Ty::Bool]);
    let mut fb = mb.function("run", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let raw = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
    let nine = fb.const_value(Ty::I64, Constant::Int(9));
    fb.store(Ty::I64, raw, nine);
    let boxed = fb.box_deref(Ty::I64, raw, premise(0, PremiseRoot::AllocPostcondition));
    // A load through the result succeeds only if it kept the provenance.
    let read = fb.load(Ty::I64, boxed);
    let before = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, raw);
    let after = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, boxed);
    let same = fb.icmp(ICmpOp::Eq, Ty::Usize, before, after);
    fb.ret(vec![read, same]);
    fb.set_body_gate(BodyGate::Ungated);
    fb.build();
    let module = mb.build().expect("the identity module builds");
    assert_eq!(validate_module(&module), vec![]);
    let outcome = trust_ir::interpret::Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("a valid Box deref executes");
    assert_eq!(outcome.returns[0].as_int().unwrap().as_signed(), 9);
    assert_eq!(outcome.returns[1].as_bool(), Some(true));
}

/// The construct presumes no pointer width: the pointee's layout comes from
/// the module's target, on which a `usize` and a pointer are four bytes for
/// a 32-bit target and eight for the 64-bit default. The same module text is
/// accepted on both, and a zero-sized pointee is outside the scope on both.
#[test]
fn the_rules_read_the_pointee_layout_of_the_module_target() {
    for target in [Some(wasm32()), None] {
        for pointee in [Ty::Usize, Ty::Ptr, Ty::U64] {
            let accepted = premised_module_on(
                target.clone(),
                pointee.clone(),
                premise(0, PremiseRoot::ParamByValue),
            );
            assert_eq!(validate_module(&accepted), vec![], "{pointee:?}");
        }
        let zero_sized = premised_module_on(
            target.clone(),
            Ty::Unit,
            premise(0, PremiseRoot::ParamByValue),
        );
        assert!(
            refusals(&zero_sized).contains(&"BoxDerefPointeeOutOfScope".to_string()),
            "{:?}",
            refusals(&zero_sized)
        );
    }
}

/// The interpreter decides the conjuncts at the target's widths: a four-byte
/// allocation holds a `usize` pointee on a 32-bit target and is too small
/// for it on the 64-bit default.
#[test]
fn the_interpreter_checks_the_conjuncts_at_the_target_width() {
    let fits = executing_module_on(Some(wasm32()), Ty::U32, Ty::Usize, |_, raw| raw);
    assert_eq!(validate_module(&fits), vec![]);
    assert_eq!(run(&fits), Ok(9));

    // Stack allocations: exact bounds, so four bytes hold the pointee only
    // where a `usize` is four bytes.
    let stack: fn(
        &mut trust_ir_build::FunctionBuilder<'_>,
        trust_ir::ValueId,
    ) -> trust_ir::ValueId = |fb, _| fb.alloca_aligned(Ty::U32, 8);
    let fits = executing_module_on(Some(wasm32()), Ty::U32, Ty::Usize, stack);
    assert_eq!(validate_module(&fits), vec![]);
    assert_eq!(run(&fits), Ok(9));
    let short = executing_module_on(None, Ty::U32, Ty::Usize, stack);
    assert_eq!(validate_module(&short), vec![]);
    let error = run(&short).expect_err("four bytes do not hold an eight-byte usize");
    assert!(
        error.contains("BoxDeref: Dereferenceable is false"),
        "{error}"
    );

    // Two bytes into a four-aligned allocation: misaligned on the 32-bit
    // target, whose pointee alignment is four.
    let misaligned = executing_module_on(Some(wasm32()), Ty::U64, Ty::Usize, |fb, raw| {
        let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, raw);
        let two = fb.const_value(Ty::Usize, Constant::Int(2));
        let moved = fb.binop(BinOp::Add, Ty::Usize, address, two);
        fb.cast(CastOp::IntToPtr, Ty::Usize, Ty::Ptr, moved)
    });
    let error = run(&misaligned).expect_err("a misaligned Box pointer on a 32-bit target");
    assert!(error.contains("Aligned is false"), "{error}");
}

/// Inlining copies a cast with its site id, so two instructions of one
/// module may carry the same id. The format judges each instruction's fact
/// and never the id.
#[test]
fn one_site_id_may_label_several_instructions() {
    let mut mb = ModuleBuilder::new("box_deref_inlined_twice");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Ptr, Ty::Ptr]);
    let mut fb = mb.function("twice", ft);
    let entry = fb.create_block();
    let first = fb.add_block_param(entry, Ty::Ptr);
    let second = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let a = fb.box_deref(Ty::I64, first, premise(7, PremiseRoot::ParamByValue));
    let b = fb.box_deref(Ty::I64, second, premise(7, PremiseRoot::ParamByValue));
    fb.ret(vec![a, b]);
    fb.set_body_gate(BodyGate::Ungated);
    fb.build();
    let module = mb.build().expect("the twice-inlined module builds");
    assert_eq!(validate_module(&module), vec![]);
}

#[test]
fn text_and_binary_carry_every_field_of_the_fact() {
    // Every evidence kind has a spelling, the two reserved ones included:
    // transport is independent of admission, and this module is refused by
    // the validator (rule 6).
    let mut module = checked_module(checked_fact());
    if let ValidityEvidence::Premise { root, .. } = &mut fact_of(&mut module).evidence[2].evidence {
        *root = PremiseRoot::ReferenceArgBoxValid;
    }
    fact_of(&mut module).site = BoxDerefSite {
        item: [
            0x00, 0x01, 0x7f, 0x80, 0xff, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x0a, 0xb0,
            0xcd, 0xef,
        ],
        ordinal: u32::MAX,
    };
    assert_eq!(
        refusals(&module),
        vec!["BoxDerefDominatingCheckInvalid".to_string()]
    );

    let text = module.to_string();
    assert!(
        text.contains(
            "site 00017f80ff102030405060700ab0cdef:4294967295, session snapshot \
             proof_session, evidence [nonnull dominating_check(), aligned \
             dominating_check(align 8), dereferenceable premise(reference_arg_box_valid; \
             safe_body, sound_callees, box_unique)], not_claimed [uniqueness, pointee_validity, \
             allocator]"
        ),
        "{text}"
    );
    let reparsed = trust_ir::parser::parse_module(&text).expect("the printed module parses");
    assert_eq!(reparsed.functions[0].blocks, module.functions[0].blocks);

    // An obligation entry travels too.
    fact_of(&mut module).evidence[2].evidence = ValidityEvidence::Obligation {
        obligation: ProofId::new(3),
    };
    let text = module.to_string();
    assert!(text.contains("dereferenceable obligation("), "{text}");
    let reparsed = trust_ir::parser::parse_module(&text).expect("the printed module parses");
    assert_eq!(reparsed.functions[0].blocks, module.functions[0].blocks);

    let bytes = trust_ir::binary::serialize_module(&module).expect("the module serializes");
    let (decoded, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("the module decodes");
    assert_eq!(
        version.get(),
        trust_ir::binary::BOX_DEREF_VALIDITY_FORMAT_VERSION
    );
    assert_eq!(decoded, module);
}

#[test]
fn the_text_parser_refuses_a_fact_it_cannot_name() {
    let module = checked_module(checked_fact());
    let text = module.to_string();
    for (from, to) in [
        ("nonnull dominating_check()", "nonzero dominating_check()"),
        ("premise(param_by_value;", "premise(somewhere;"),
        ("safe_body, sound_callees", "safe_body, kind_callees"),
        ("session snapshot", "session guess"),
        ("proof_session", "value_neutral"),
        ("[uniqueness,", "[everything,"),
        ("dominating_check(align 8)", "trusted(align 8)"),
        (
            ", not_claimed [uniqueness, pointee_validity, allocator]",
            "",
        ),
    ] {
        assert!(text.contains(from), "the subject spells `{from}`");
        let edited = text.replacen(from, to, 1);
        assert!(
            trust_ir::parser::parse_module(&edited).is_err(),
            "`{from}` -> `{to}` must not parse"
        );
    }
}

/// The four code-generation targets of the Box program, as modules name
/// them. Nothing in the rules reads the triple; only the pointer width
/// reaches the pointee layout.
fn parity_targets() -> [TargetInfo; 4] {
    let target = |triple: &str, pointer_size: u32| TargetInfo {
        triple: triple.into(),
        pointer_size,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    };
    [
        target("x86_64-unknown-linux-gnu", 8),
        target("aarch64-apple-darwin", 8),
        target("wasm32-unknown-unknown", 4),
        target("riscv64gc-unknown-linux-gnu", 8),
    ]
}

/// One acceptance check for every target: the same module shape is accepted
/// on each, every mutation is refused by the same rule on each, the evidence
/// floor gives the same verdict on each, and the interpreter gives the same
/// outcome on each. The pointee is a `u64`, whose size and alignment do not
/// depend on the pointer width, so the four modules differ in their target
/// alone. The control holds a premise and no assert, so no target's
/// consumer needs a route for a failing check to accept it.
///
/// This is a host-side check of modules that NAME each target. It executes
/// no target code.
#[test]
fn the_acceptance_check_and_its_refusals_are_the_same_on_every_target() {
    type Mutation = (&'static str, fn(&mut BoxValidityFact));
    let mutations: &[Mutation] = &[
        ("drop a conjunct", |fact| {
            fact.evidence.remove(1);
        }),
        ("empty the standing assumptions", |fact| {
            if let ValidityEvidence::Premise { standing, .. } = &mut fact.evidence[2].evidence {
                standing.clear();
            }
        }),
        ("state a session whose verifier did not run", |fact| {
            fact.session.producing = ProducingSession::NonProofSession;
        }),
        ("judge on the fallback body", |fact| {
            fact.session.judged = JudgedBody::OptimizedFallback;
        }),
        ("offer a check for non-nullness", |fact| {
            fact.evidence[0].evidence = ValidityEvidence::DominatingCheck { align: None };
        }),
        ("offer a check for alignment", |fact| {
            fact.evidence[1].evidence = ValidityEvidence::DominatingCheck { align: Some(8) };
        }),
        ("cite an obligation", |fact| {
            fact.evidence[2].evidence = ValidityEvidence::Obligation {
                obligation: ProofId::new(7),
            };
        }),
        ("premise one conjunct on another root", |fact| {
            if let ValidityEvidence::Premise { root, .. } = &mut fact.evidence[2].evidence {
                *root = PremiseRoot::ReferenceArgBoxValid;
            }
        }),
        ("drop a non-claim", |fact| {
            fact.not_claimed.remove(0);
        }),
    ];

    let verdicts = |target: TargetInfo| -> Vec<(String, Vec<String>)> {
        let control = premised_module_on(
            Some(target.clone()),
            Ty::U64,
            premise(0, PremiseRoot::ParamByValue),
        );
        assert!(
            control.functions[0].blocks[0]
                .body
                .iter()
                .all(|node| !matches!(node.inst, Inst::Assert { .. })),
            "the control holds no assert"
        );
        let mut out = vec![("control".to_string(), refusals(&control))];
        for (what, mutate) in mutations {
            let mut module = control.clone();
            mutate(fact_of(&mut module));
            out.push((what.to_string(), refusals(&module)));
        }
        let assumed = premised_module_on(
            Some(target.clone()),
            Ty::U64,
            premise(0, PremiseRoot::ReferenceArgBoxValid),
        );
        for (name, module) in [("named", &control), ("assumed", &assumed)] {
            for floor in [None]
                .into_iter()
                .chain(BoxValidityTier::ALL.into_iter().map(Some))
            {
                let admission =
                    CodegenAdmission::pinned().with_require_box_validity_evidence(floor);
                let mut names: Vec<String> = validate_module_for_codegen_with(module, &admission)
                    .into_iter()
                    .filter(|error| {
                        matches!(error, ValidationError::BoxValidityEvidenceBelowFloor { .. })
                    })
                    .map(|error| error.to_string())
                    .collect();
                names.dedup();
                out.push((format!("{name} root, floor {floor:?}"), names));
            }
        }
        let valid = executing_module_on(Some(target.clone()), Ty::U64, Ty::U64, |_, raw| raw);
        out.push(("valid: validator".to_string(), refusals(&valid)));
        out.push((
            "interpreter: valid".to_string(),
            vec![format!("{:?}", run(&valid))],
        ));
        let null = executing_module_on(Some(target), Ty::U64, Ty::U64, |fb, _| fb.null_ptr());
        out.push(("null: validator".to_string(), refusals(&null)));
        out.push((
            "interpreter: null".to_string(),
            vec![format!("{:?}", run(&null))],
        ));
        out
    };

    let [first, rest @ ..] = parity_targets();
    let expected = verdicts(first.clone());
    // The shared verdicts are the intended ones, not merely equal ones.
    assert_eq!(expected[0], ("control".to_string(), vec![]));
    assert!(
        expected[1..=mutations.len()]
            .iter()
            .all(|(_, names)| names.len() == 1 && names[0].starts_with("BoxDeref")),
        "{expected:?}"
    );
    let verdict = |name: &str| -> &Vec<String> {
        &expected
            .iter()
            .find(|(what, _)| what == name)
            .unwrap_or_else(|| panic!("no verdict named {name}"))
            .1
    };
    assert!(verdict("named root, floor Some(NamedPremise)").is_empty());
    assert_eq!(verdict("assumed root, floor Some(NamedPremise)").len(), 3);
    assert!(verdict("assumed root, floor Some(AssumedRootPremise)").is_empty());
    assert_eq!(
        verdict("named root, floor Some(ConsumerRederived)").len(),
        3
    );
    assert!(verdict("valid: validator").is_empty());
    assert_eq!(
        verdict("null: validator"),
        &vec!["BoxDerefPremiseContradicted".to_string()]
    );
    for target in rest {
        assert_eq!(
            verdicts(target.clone()),
            expected,
            "{} vs {}",
            target.triple,
            first.triple
        );
    }
}
