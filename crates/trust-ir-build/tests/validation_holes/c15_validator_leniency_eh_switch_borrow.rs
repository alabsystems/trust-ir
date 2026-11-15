// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Claim c15 (F-032 with the F-039 / F-040 / F-021 / F-018 / F-041 legs):
//! validator leniency on exception-handling placement, the switch
//! exhaustiveness flag, borrow discipline, claim-style attributes and the
//! proof table.
//!
//! Source: `reports/2026-09-17-two-language-proof-program/verify/c15_validator_leniency_eh_switch_borrow/`.
//! Each sub-claim is a validating baseline plus ONE mutation.
//!
//! * (1) EH placement and (6a) a pad entered by a plain `Br`: CLOSED UPSTREAM
//!   by WS2.5 (`5a945757`, `b3a1b963`). Only the flipped twins land here, on
//!   the skeptic's exact modules, each refused with its named error.
//! * (5d) a dangling `obligation.function`: CLOSED UPSTREAM by `5a945757`
//!   (the early WS1.8 B4 item). Flipped twin.
//! * (2) `Switch.exhaustive_enum_unreachable` had no validator reader
//!   (F-039): CLOSED by WS2.6. 2a/2b land as flipped twins
//!   (`ExhaustiveSwitchDefaultReachable` / `ExhaustiveSwitchCasesIncomplete`),
//!   2c as the mutation control that still validates, beside per-clause
//!   twins of both rules.
//! * (3) borrow discipline (F-040): the STRUCTURAL half is CLOSED UPSTREAM by
//!   WS2.7 (`5f28fc7e`, `6f3fbcdc`) — 3a and 3g land as flipped twins
//!   (`BorrowMutThroughSharedRef`); the LIVENESS half (3b-3f) is ratified as a
//!   producer obligation (`TRUST.md` item 12, `LIMITATIONS.md`), so those rows
//!   land as `ratified_*` positive fixtures, not ratchets.
//! * (4) memory-effect claims on a storing body (F-021): `readnone` /
//!   `readonly` (4a/4b) are CLOSED UPSTREAM by WS2.7 (`FuncAttrClaimViolated`,
//!   flipped twins); a function-level `Pure` annotation (4c) is outside
//!   WS2.7's `FuncAttrs` rule and stays a GAP ratchet.
//! * (5a/5b/5e) certificates on Pending/Failed rows and a certificate-free
//!   Trusted row (F-018, WS1.8 flips them).
//!
//! The `gap_*` rows are ratchets asserting today's acceptance. The `control_*`
//! rows show the neighbouring rule that IS enforced.

use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::proof::{
    ObligationKind, ObligationSite, ProofCertificate, ProofEvidence, ProofObligation, ProofStatus,
    RejectingModuleProofAuthority,
};
use trust_ir::ty::{EnumDef, EnumTagRepr, EnumVariant};
use trust_ir::value::{BlockId, EnumId, FuncId, ValueId};
use trust_ir::{BodyGate, Constant, FuncAttrs, Inst, Module, ProofAnnotation, SwitchCase, Ty};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    ModuleBuilder, validate_module, validate_module_for_codegen, validate_module_with_authority,
};

fn gate() -> BodyGate {
    BodyGate::Gated {
        authority: "c15-repro".to_string(),
        evidence: None,
    }
}

/// An authority that admits every certificate: the (5) rows hold even under it.
struct AdmitAll;
impl trust_ir::proof::ModuleProofAuthority for AdmitAll {
    fn replays_authority(&self, _: &Module, _: &ProofObligation, _: &ProofCertificate) -> bool {
        true
    }
}

/// The structural tier reports exactly `expected`, and the codegen and both
/// authority-tier entry points report each of them too — no weaker finding
/// may stand in for the named one.
fn assert_refused_everywhere(tag: &str, m: &Module, expected: &[ValidationError]) {
    assert_eq!(validate_module(m), expected, "{tag}: structural tier");
    for (tier, errors) in [
        ("codegen", validate_module_for_codegen(m)),
        (
            "rejecting authority",
            validate_module_with_authority(m, &RejectingModuleProofAuthority),
        ),
        (
            "admit-all authority",
            validate_module_with_authority(m, &AdmitAll),
        ),
    ] {
        for e in expected {
            assert!(
                errors.contains(e),
                "{tag}: {tier} tier lacks {e:?}: {errors:?}"
            );
        }
    }
}

/// Clean under the plain, codegen, and both authority-tier entry points.
fn assert_accepted_everywhere(tag: &str, m: &Module) {
    assert_eq!(validate_module(m), Vec::new(), "{tag}");
    assert_eq!(validate_module_for_codegen(m), Vec::new(), "{tag}");
    assert_eq!(
        validate_module_with_authority(m, &RejectingModuleProofAuthority),
        Vec::new(),
        "{tag}"
    );
    assert_eq!(
        validate_module_with_authority(m, &AdmitAll),
        Vec::new(),
        "{tag}"
    );
}

// ---------------------------------------------------------------------------
// (1) EH placement — closed upstream; flipped twins
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum Eh {
    Baseline,
    /// `unwind_dest` block has NO LandingPad (just `unreachable`).
    NoPad,
    /// LandingPad is the first instruction of the ENTRY block.
    PadInEntry,
    /// LandingPad is NOT the first instruction of the unwind block.
    PadNotFirst,
    /// `unwind_dest == normal_dest`.
    UnwindIsNormal,
}

fn eh_module(kind: Eh) -> Module {
    let mut mb = ModuleBuilder::new("c15_eh");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let callee = {
        let mut fb = mb.function("callee", sig);
        fb.set_body_gate(gate());
        let b = fb.create_block();
        fb.switch_to_block(b);
        let v = fb.iconst(Ty::U64, 7);
        fb.ret(vec![v]);
        fb.build()
    };
    let mut fb = mb.function("program", sig);
    fb.set_body_gate(gate());
    let entry = fb.create_block();
    let normal = fb.create_block();
    let pad = fb.create_block();
    fb.switch_to_block(entry);
    if kind == Eh::PadInEntry {
        let _ = fb.landingpad(true, vec![]);
    }
    let unwind = if kind == Eh::UnwindIsNormal {
        normal
    } else {
        pad
    };
    let r = fb.invoke(callee, vec![], normal, vec![], unwind);
    fb.switch_to_block(normal);
    if kind == Eh::UnwindIsNormal {
        let c = fb.iconst(Ty::U64, 1);
        fb.ret(vec![c]);
    } else {
        fb.ret(vec![r]);
    }
    fb.switch_to_block(pad);
    match kind {
        Eh::NoPad | Eh::UnwindIsNormal => fb.unreachable(),
        Eh::PadNotFirst => {
            let _ = fb.iconst(Ty::U64, 0);
            let (exn, _sel) = fb.landingpad(true, vec![]);
            fb.resume(exn);
        }
        Eh::Baseline | Eh::PadInEntry => {
            let (exn, _sel) = fb.landingpad(true, vec![]);
            fb.resume(exn);
        }
    }
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    if kind == Eh::UnwindIsNormal {
        let f = m
            .functions
            .iter_mut()
            .find(|f| f.name == "program")
            .unwrap();
        f.blocks.truncate(2);
    }
    m
}

/// Row `verify.c15` 1a-1d, flipped (closed upstream by WS2.5): each misplaced
/// unwind shape is refused with its named placement error, and the positive
/// baseline still validates.
#[test]
fn c15_flipped_landingpad_placement_is_checked() {
    assert_accepted_everywhere("1.baseline", &eh_module(Eh::Baseline));

    let errors = validate_module(&eh_module(Eh::NoPad));
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::UnwindDestWithoutLandingPad { .. })),
        "1a: {errors:?}"
    );
    for (tag, kind) in [
        ("1b pad in entry", Eh::PadInEntry),
        ("1c pad not first", Eh::PadNotFirst),
    ] {
        let errors = validate_module(&eh_module(kind));
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::MisplacedLandingPad { .. })),
            "{tag}: {errors:?}"
        );
    }
    let errors = validate_module(&eh_module(Eh::UnwindIsNormal));
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::UnwindDestWithoutLandingPad { .. })),
        "1d: {errors:?}"
    );
}

/// Row `verify.c15` 6a, flipped (closed upstream by WS2.5): a landing-pad
/// block entered by a plain `Br` is refused.
#[test]
fn c15_flipped_landingpad_block_entered_by_plain_br() {
    let mut mb = ModuleBuilder::new("c15_resume");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    fb.set_body_gate(gate());
    let entry = fb.create_block();
    let pad = fb.create_block();
    fb.switch_to_block(entry);
    fb.br(pad, vec![]);
    fb.switch_to_block(pad);
    let (exn, _) = fb.landingpad(true, vec![]);
    fb.resume(exn);
    fb.build();
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::MisplacedLandingPad { .. })),
        "{errors:?}"
    );
}

/// Mutation control: the pre-WS2.5 rule (a parameter-free unwind block) is
/// still enforced.
#[test]
fn c15_control_parameterised_unwind_block_is_refused() {
    let mut m = eh_module(Eh::Baseline);
    let f = m
        .functions
        .iter_mut()
        .find(|f| f.name == "program")
        .unwrap();
    f.blocks[2].params.push((ValueId::new(900), Ty::Ptr));
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::BranchArgCountMismatch {
                expected: 1,
                actual: 0,
                ..
            }
        )),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// (2) Switch.exhaustive_enum_unreachable (F-039)
// ---------------------------------------------------------------------------

fn enum_def(n: usize) -> EnumDef {
    EnumDef::new(
        EnumId::new(0),
        "E",
        (0..n)
            .map(|i| EnumVariant {
                name: format!("V{i}"),
                fields: vec![],
                field_names: vec![],
            })
            .collect(),
    )
    .with_repr(EnumTagRepr::U8)
}

/// `pick(e: E) -> u64`: `switch extract_field(e, 0) {0 -> 10, 1 -> 11}` with a
/// default that is `unreachable` or LIVE (returns 99); `program()` calls
/// `pick` with the variant `run_tag`.
fn switch_module(variants: usize, flag: bool, live_default: bool, run_tag: i128) -> Module {
    switch_module_over(enum_def(variants), flag, live_default, run_tag)
}

/// [`switch_module`] over an arbitrary `E` definition (id 0).
fn switch_module_over(def: EnumDef, flag: bool, live_default: bool, run_tag: i128) -> Module {
    let e = Ty::Enum(EnumId::new(0));
    let mut mb = ModuleBuilder::new("c15_switch");
    let pick_sig = mb.add_func_type(vec![e.clone()], vec![Ty::U64]);
    let main_sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let pick = {
        let mut fb = mb.function("pick", pick_sig);
        fb.set_body_gate(gate());
        let entry = fb.create_block();
        let a = fb.create_block();
        let b = fb.create_block();
        let d = fb.create_block();
        let p = fb.add_block_param(entry, e.clone());
        fb.switch_to_block(entry);
        let tag = fb.extract_field(Ty::U8, p, 0);
        fb.switch(
            tag,
            vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: a,
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: b,
                    args: vec![],
                },
            ],
            d,
            vec![],
        );
        fb.switch_to_block(a);
        let va = fb.iconst(Ty::U64, 10);
        fb.ret(vec![va]);
        fb.switch_to_block(b);
        let vb = fb.iconst(Ty::U64, 11);
        fb.ret(vec![vb]);
        fb.switch_to_block(d);
        if live_default {
            let vd = fb.iconst(Ty::U64, 99);
            fb.ret(vec![vd]);
        } else {
            fb.unreachable();
        }
        fb.build()
    };
    {
        let mut fb = mb.function("program", main_sig);
        fb.set_body_gate(gate());
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.const_value(e, Constant::Aggregate(vec![Constant::Int(run_tag)]));
        let r = fb.call(pick, vec![v]);
        fb.ret(vec![r]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_enum(def);
    if flag {
        let f = m.functions.iter_mut().find(|f| f.name == "pick").unwrap();
        for node in &mut f.blocks[0].body {
            if let Inst::Switch {
                exhaustive_enum_unreachable,
                ..
            } = &mut node.inst
            {
                *exhaustive_enum_unreachable = true;
            }
        }
    }
    m
}

fn run_program(m: &Module) -> Result<u128, String> {
    let id = m.function_by_name("program").expect("program").id;
    Interpreter::with_module(m)
        .execute_func(id, Vec::new())
        .map(|o| o.returns[0].as_int().expect("int").as_unsigned())
        .map_err(|e| format!("{:?}: {e}", e.code))
}

/// `u8` switch `{0 -> ret 1}` whose default is `unreachable`, flag set iff
/// `flag`: no enum anywhere, so only WS2.6 rule 1 can apply.
fn plain_u8_switch(flag: bool, extra_case: Option<i128>) -> Module {
    let mut mb = ModuleBuilder::new("c15_switch_int");
    let sig = mb.add_func_type(vec![Ty::U8], vec![Ty::U64]);
    let mut fb = mb.function("f", sig);
    fb.set_body_gate(gate());
    let entry = fb.create_block();
    let a = fb.create_block();
    let d = fb.create_block();
    let p = fb.add_block_param(entry, Ty::U8);
    fb.switch_to_block(entry);
    let mut cases = vec![SwitchCase {
        value: Constant::Int(0),
        target: a,
        args: vec![],
    }];
    if let Some(v) = extra_case {
        cases.push(SwitchCase {
            value: Constant::Int(v),
            target: a,
            args: vec![],
        });
    }
    fb.switch(p, cases, d, vec![]);
    fb.switch_to_block(a);
    let va = fb.iconst(Ty::U64, 1);
    fb.ret(vec![va]);
    fb.switch_to_block(d);
    fb.unreachable();
    fb.build();
    let mut plain = mb.build().expect("ModuleBuilder::build: test fixture");
    if let Inst::Switch {
        exhaustive_enum_unreachable,
        ..
    } = &mut plain.functions[0].blocks[0].body[0].inst
    {
        *exhaustive_enum_unreachable = flag;
    }
    plain
}

fn default_reachable(reason: &str) -> ValidationError {
    ValidationError::ExhaustiveSwitchDefaultReachable {
        block: 0,
        reason: reason.to_string(),
    }
}

/// SPEC_RATIFICATIONS §3.3: switch case `index` of `f`'s entry block is no
/// value of the selector type `ty` — the constant funnel's refusal of its
/// `Inst::Const` twin, located at the case.
fn case_out_of_range(index: usize, ty: &str) -> ValidationError {
    ValidationError::ConstTypeMismatch {
        location: format!("function 'f' bb0 switch case {index}"),
        expected: ty.to_string(),
        actual: "int".to_string(),
    }
}

fn cases_incomplete(reason: &str) -> ValidationError {
    ValidationError::ExhaustiveSwitchCasesIncomplete {
        block: 0,
        enum_ty: Ty::Enum(EnumId::new(0)).to_string(),
        reason: reason.to_string(),
    }
}

/// `pick`'s flagged switch.
fn pick_switch(m: &mut Module) -> &mut Inst {
    let f = m.functions.iter_mut().find(|f| f.name == "pick").unwrap();
    &mut f.blocks[0].body.last_mut().unwrap().inst
}

/// Row `verify.c15` 2a/2b/2c, flipped (WS2.6, F-039): the flag is read.
/// 2a — stamped on a switch whose default is LIVE — is exactly
/// `ExhaustiveSwitchDefaultReachable`; 2b — the enum gains a third, inhabited
/// variant the `{0, 1}` case set does not cover — is exactly
/// `ExhaustiveSwitchCasesIncomplete`, in every tier. 2c, the MUTATION
/// CONTROL: the flag on a plain `u8` switch whose default is `[unreachable]`
/// still validates — the rule states only what it checks, and a plain
/// integer's case set is not something it checks.
#[test]
fn c15_flipped_switch_exhaustive_flag_is_read() {
    let live = switch_module(2, true, true, 1);
    assert_refused_everywhere(
        "2a live default",
        &live,
        &[default_reachable(
            "the default block bb3 is not exactly [unreachable] (2 instruction(s))",
        )],
    );
    // Control: the same module without the claim is a legal switch.
    assert_accepted_everywhere("2a unflagged", &switch_module(2, false, true, 1));

    let uncovered = switch_module(3, true, false, 2);
    assert_refused_everywhere(
        "2b third variant",
        &uncovered,
        &[cases_incomplete(
            "no case for inhabited variant(s) {V2 = 2}, so the default arm is reachable",
        )],
    );
    assert!(
        run_program(&uncovered).is_err(),
        "tag 2 reaches the unreachable default"
    );
    // Control: without the claim, a partial match with an unreachable default
    // is the producer's (UB-bearing) business, not a format violation.
    assert_accepted_everywhere("2b unflagged", &switch_module(3, false, false, 2));

    let plain = plain_u8_switch(true, None);
    assert_accepted_everywhere("2c plain u8", &plain);
    let f = plain.functions[0].id;
    let five = InterpretValue::int(Ty::U8, 5).unwrap();
    assert!(
        Interpreter::with_module(&plain)
            .execute_func(f, vec![five])
            .is_err()
    );
}

/// WS2.6 rule 1, clause by clause: each is one mutation of the positive
/// baseline and each is named. A syntactic repeat stays the pre-existing
/// `DuplicateSwitchCase` alone (never doubled); an ALIAS under the selector
/// width (`0` and `256` at `u8`) is the flagged switch's own refusal. Since
/// SPEC_RATIFICATIONS §3.3 the alias's out-of-range spelling (`256` is no `u8`
/// value) is ALSO refused at the case by the constant funnel, flag or no flag;
/// the alias this clause alone sees is in
/// `c15_review_exhaustive_flag_alias_at_pointer_width_and_char`.
#[test]
fn c15_exhaustive_flag_default_edge_clauses() {
    // (i)+(ii): the default block takes a parameter and the edge passes one.
    let mut m = switch_module(2, true, false, 1);
    {
        let f = m.functions.iter_mut().find(|f| f.name == "pick").unwrap();
        let arg = f.blocks[0].params[0].0;
        let d = f.blocks.iter_mut().find(|b| b.id.index() == 3).unwrap();
        d.params.push((ValueId::new(900), Ty::Enum(EnumId::new(0))));
        if let Inst::Switch { default_args, .. } = &mut f.blocks[0].body.last_mut().unwrap().inst {
            default_args.push(arg);
        }
    }
    assert_refused_everywhere(
        "(i)+(ii) default edge with an argument",
        &m,
        &[
            default_reachable(
                "the default edge to bb3 passes 1 argument(s); a dead default carries none",
            ),
            default_reachable("the default block bb3 has 1 parameter(s); a dead default has none"),
        ],
    );

    // (ii): a dead default must be EXACTLY [unreachable] — an instruction
    // before it is refused.
    let mut m = switch_module(2, true, false, 1);
    {
        let f = m.functions.iter_mut().find(|f| f.name == "pick").unwrap();
        let d = f.blocks.iter_mut().find(|b| b.id.index() == 3).unwrap();
        d.body.insert(
            0,
            trust_ir::InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(901)),
        );
    }
    assert_refused_everywhere(
        "(ii) extra instruction",
        &m,
        &[default_reachable(
            "the default block bb3 is not exactly [unreachable] (2 instruction(s))",
        )],
    );

    // (iii): 0 and 256 are one u8 selector value.
    assert_refused_everywhere(
        "(iii) alias",
        &plain_u8_switch(true, Some(256)),
        &[
            default_reachable("case values 0 and 256 denote the same u8 selector value"),
            case_out_of_range(1, "u8"),
        ],
    );
    // Unflagged, (iii) says nothing, and §3.3 still refuses the spelling.
    assert_refused_everywhere(
        "(iii) alias unflagged",
        &plain_u8_switch(false, Some(256)),
        &[case_out_of_range(1, "u8")],
    );
    // A syntactic repeat is DuplicateSwitchCase, once.
    assert_eq!(
        validate_module(&plain_u8_switch(true, Some(0))),
        vec![ValidationError::DuplicateSwitchCase {
            block: 0,
            value: "0".to_string(),
        }]
    );
}

/// `E` with `V0`, `V1` (fieldless) and `V2` carrying one field of type `field`.
fn enum_with_v2(field: Ty) -> EnumDef {
    let mut def = enum_def(3);
    def.variants[2].fields = vec![field];
    def
}

/// WS2.6 rule 2 against the enum: a case value that is no discriminant is
/// refused; an omitted variant is admitted exactly when the validator can
/// PROVE it uninhabited by structure (a by-value `Never`, a zero-variant enum,
/// through by-value tuple / non-empty array containment), and refused for
/// everything it cannot (behind a reference, in an empty array). The
/// selector is traced through `Copy`.
#[test]
fn c15_exhaustive_flag_case_set_against_the_enum() {
    // A stray case value 7 (routed to an existing arm).
    let mut m = switch_module(2, true, false, 1);
    if let Inst::Switch { cases, .. } = pick_switch(&mut m) {
        let target = cases[0].target;
        cases.push(SwitchCase {
            value: Constant::Int(7),
            target,
            args: vec![],
        });
    }
    assert_refused_everywhere(
        "stray case",
        &m,
        &[cases_incomplete(&format!(
            "case value 7 is not a discriminant of {}",
            Ty::Enum(EnumId::new(0))
        ))],
    );

    // Proven uninhabited: the omitted V2 is admitted.
    let admitted = |tag: &str, m: &mut Module, field: Ty| {
        m.enums[0] = enum_with_v2(field);
        assert_accepted_everywhere(tag, m);
    };
    let mut m = switch_module(2, true, false, 1);
    admitted("V2(!)", &mut m, Ty::Never);
    let mut m = switch_module(2, true, false, 1);
    admitted("V2((u8, !))", &mut m, Ty::Tuple(vec![Ty::U8, Ty::Never]));
    let mut m = switch_module(2, true, false, 1);
    let never = m
        .add_type(Ty::Never)
        .expect("Module::add_type: test fixture");
    admitted("V2([!; 2])", &mut m, Ty::Array(never, 2));

    // NOT proven uninhabited: the omitted V2 is refused.
    let refused = |tag: &str, m: &mut Module, field: Ty| {
        m.enums[0] = enum_with_v2(field);
        let errors = validate_module(m);
        assert!(
            errors.contains(&cases_incomplete(
                "no case for inhabited variant(s) {V2 = 2}, so the default arm is reachable",
            )),
            "{tag}: {errors:?}"
        );
    };
    let mut m = switch_module(2, true, false, 1);
    refused("V2(&!)", &mut m, Ty::Ref(Box::new(Ty::Never)));
    let mut m = switch_module(2, true, false, 1);
    let never = m
        .add_type(Ty::Never)
        .expect("Module::add_type: test fixture");
    refused("V2([!; 0])", &mut m, Ty::Array(never, 0));
    let mut m = switch_module(2, true, false, 1);
    refused("V2(u64)", &mut m, Ty::U64);

    // Through `Copy`: the selector is a copy of the tag read.
    let mut m = switch_module(3, true, false, 1);
    {
        let f = m.functions.iter_mut().find(|f| f.name == "pick").unwrap();
        let body = &mut f.blocks[0].body;
        let tag = body[0].results[0];
        let copy = ValueId::new(902);
        body.insert(
            1,
            trust_ir::InstrNode::new(Inst::Copy {
                ty: Ty::U8,
                operand: tag,
            })
            .with_result(copy),
        );
        if let Inst::Switch { value, .. } = &mut body.last_mut().unwrap().inst {
            *value = copy;
        }
    }
    assert_refused_everywhere(
        "through copy",
        &m,
        &[cases_incomplete(
            "no case for inhabited variant(s) {V2 = 2}, so the default arm is reachable",
        )],
    );
}

/// A flagged switch over a `ty` block parameter with the given case values,
/// every case returning 1 and the default `[unreachable]`: no enum anywhere,
/// so only rule 1 applies.
fn plain_switch(ty: Ty, values: &[Constant]) -> Module {
    let mut mb = ModuleBuilder::new("c15_switch_plain");
    let sig = mb.add_func_type(vec![ty.clone()], vec![Ty::U64]);
    let mut fb = mb.function("f", sig);
    fb.set_body_gate(gate());
    let entry = fb.create_block();
    let a = fb.create_block();
    let d = fb.create_block();
    let p = fb.add_block_param(entry, ty);
    fb.switch_to_block(entry);
    let cases = values
        .iter()
        .map(|v| SwitchCase {
            value: v.clone(),
            target: a,
            args: vec![],
        })
        .collect();
    fb.switch(p, cases, d, vec![]);
    fb.switch_to_block(a);
    let va = fb.iconst(Ty::U64, 1);
    fb.ret(vec![va]);
    fb.switch_to_block(d);
    fb.unreachable();
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    if let Inst::Switch {
        exhaustive_enum_unreachable,
        ..
    } = &mut m.functions[0].blocks[0].body[0].inst
    {
        *exhaustive_enum_unreachable = true;
    }
    m
}

/// `pick(e: E) -> u64` over `def`: the tag lane read at `tag_ty`, then widened
/// by each `(op, dst)` cast in turn — the Trust bridge's
/// `Rvalue::Discriminant` shape (`extract_field` at the canonical tag repr,
/// then ONE `sext`/`zext`/`bitcast` to the MIR discriminant type) — and
/// switched on with the flag set. Every case returns 1; the default is
/// `[unreachable]`.
fn widened_switch_module(
    def: EnumDef,
    tag_ty: Ty,
    casts: &[(trust_ir::CastOp, Ty)],
    values: &[Constant],
) -> Module {
    let e = Ty::Enum(EnumId::new(0));
    let mut mb = ModuleBuilder::new("c15_switch_widened");
    let sig = mb.add_func_type(vec![e.clone()], vec![Ty::U64]);
    let mut fb = mb.function("pick", sig);
    fb.set_body_gate(gate());
    let entry = fb.create_block();
    let a = fb.create_block();
    let d = fb.create_block();
    let p = fb.add_block_param(entry, e);
    fb.switch_to_block(entry);
    let mut sel = fb.extract_field(tag_ty.clone(), p, 0);
    let mut sel_ty = tag_ty;
    for (op, dst) in casts {
        sel = fb.cast(*op, sel_ty, dst.clone(), sel);
        sel_ty = dst.clone();
    }
    let cases = values
        .iter()
        .map(|v| SwitchCase {
            value: v.clone(),
            target: a,
            args: vec![],
        })
        .collect();
    fb.switch(sel, cases, d, vec![]);
    fb.switch_to_block(a);
    let va = fb.iconst(Ty::U64, 1);
    fb.ret(vec![va]);
    fb.switch_to_block(d);
    fb.unreachable();
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_enum(def);
    if let Inst::Switch {
        exhaustive_enum_unreachable,
        ..
    } = pick_switch(&mut m)
    {
        *exhaustive_enum_unreachable = true;
    }
    m
}

fn ints(values: &[i128]) -> Vec<Constant> {
    values.iter().map(|v| Constant::Int(*v)).collect()
}

/// Review (WS2.6), adversarial: rule 1's distinctness clause at the
/// selector types whose width `Ty::bit_width` leaves unresolved or that
/// `is_integer` does not admit. `usize`/`isize` execute at the target's
/// pointer width (the reference interpreter's 64), and `char` is a 32-bit
/// carrier, so `0` and `2^64` (resp. `2^32`) are ONE selector value there —
/// the flagged switch's second case is dead, and the claim "distinct cases"
/// is false. Before the review both validated. Since SPEC_RATIFICATIONS §3.3
/// each of those aliases is also no value of its selector type, refused at
/// the case by the constant funnel — on a 32-bit target too, where the funnel
/// checks `usize` at the target's 32 bits (since 2026-10-01; before, it
/// checked 64 bits on every target, so `0` and `2^32` were both admitted
/// cases there and the alias was THIS clause's alone).
#[test]
fn c15_review_exhaustive_flag_alias_at_pointer_width_and_char() {
    let two64 = 1i128 << 64;
    assert_refused_everywhere(
        "usize alias",
        &plain_switch(Ty::Usize, &ints(&[0, two64])),
        &[
            default_reachable(&format!(
                "case values 0 and {two64} denote the same usize selector value"
            )),
            case_out_of_range(1, "usize"),
        ],
    );
    assert_refused_everywhere(
        "isize alias",
        &plain_switch(Ty::Isize, &ints(&[-1, two64 - 1])),
        &[
            default_reachable(&format!(
                "case values -1 and {} denote the same isize selector value",
                two64 - 1
            )),
            case_out_of_range(1, "isize"),
        ],
    );
    let two32 = 1i128 << 32;
    assert_refused_everywhere(
        "char alias",
        &plain_switch(Ty::Char, &ints(&[65, two32 + 65])),
        &[
            default_reachable(&format!(
                "case values 65 and {} denote the same char selector value",
                two32 + 65
            )),
            ValidationError::ConstTypeMismatch {
                location: "function 'f' bb0 switch case 1".to_string(),
                expected: "a Unicode scalar value (0..=0x10FFFF minus 0xD800..=0xDFFF)".to_string(),
                actual: format!("char constant {}", two32 + 65),
            },
            case_out_of_range(1, "char"),
        ],
    );
    // The 32-bit alias: `0` and `2^32` are one `usize` selector value on a
    // 32-bit target, and `2^32` is no `usize` constant there.
    let mut wasm32 = plain_switch(Ty::Usize, &ints(&[0, two32]));
    wasm32.target_info = Some(trust_ir::TargetInfo {
        triple: "wasm32-unknown-unknown".into(),
        pointer_size: 4,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    assert_refused_everywhere(
        "usize alias on a 32-bit target",
        &wasm32,
        &[
            default_reachable(&format!(
                "case values 0 and {two32} denote the same usize selector value"
            )),
            case_out_of_range(1, "usize"),
        ],
    );
    // Controls: distinct values at the same types still validate — at the
    // default 64-bit pointer width `2^32` is its own `usize` value.
    assert_accepted_everywhere(
        "usize distinct",
        &plain_switch(Ty::Usize, &ints(&[0, two32])),
    );
    assert_accepted_everywhere("char distinct", &plain_switch(Ty::Char, &ints(&[0, 65])));
}

/// Review (WS2.6), adversarial: the real producer never switches on the
/// `extract_field` result itself. The Trust bridge's `Rvalue::Discriminant`
/// reads the tag at the canonical repr and widens it with ONE cast to the MIR
/// discriminant type (`sext` for a signed repr, `zext` for unsigned,
/// `bitcast` at equal width). Tracing only `Copy` let a 2-of-3 case set
/// through a widening cast validate — rule 2 never saw the producer's shape.
#[test]
fn c15_review_exhaustive_flag_traces_widening_casts() {
    use trust_ir::CastOp;
    let e_ty = Ty::Enum(EnumId::new(0)).to_string();
    let incomplete = |missing: &str| ValidationError::ExhaustiveSwitchCasesIncomplete {
        block: 0,
        enum_ty: e_ty.clone(),
        reason: format!(
            "no case for inhabited variant(s) {{{missing}}}, so the default arm is reachable"
        ),
    };
    let stray = |value: &str| ValidationError::ExhaustiveSwitchCasesIncomplete {
        block: 0,
        enum_ty: e_ty.clone(),
        reason: format!("case value {value} is not a discriminant of {e_ty}"),
    };

    // u8 tag, zext to isize (the bridge's Option-like shape): {0, 1} of 3.
    let m = widened_switch_module(
        enum_def(3),
        Ty::U8,
        &[(CastOp::ZExt, Ty::Isize)],
        &ints(&[0, 1]),
    );
    assert_refused_everywhere("zext 2-of-3", &m, &[incomplete("V2 = 2")]);
    // Positive: the full set through the same cast.
    let m = widened_switch_module(
        enum_def(3),
        Ty::U8,
        &[(CastOp::ZExt, Ty::Isize)],
        &ints(&[0, 1, 2]),
    );
    assert_accepted_everywhere("zext full", &m);

    // A signed repr: discriminants {-1, 0, 1} at i8, sext to i64.
    let signed = || {
        EnumDef::new(
            EnumId::new(0),
            "E",
            (0..3)
                .map(|i| EnumVariant {
                    name: format!("V{i}"),
                    fields: vec![],
                    field_names: vec![],
                })
                .collect(),
        )
        .with_discriminants(vec![Some(-1), Some(0), Some(1)])
        .with_repr(EnumTagRepr::I8)
    };
    let m = widened_switch_module(
        signed(),
        Ty::I8,
        &[(CastOp::SExt, Ty::I64)],
        &ints(&[-1, 0, 1]),
    );
    assert_accepted_everywhere("sext full", &m);
    let m = widened_switch_module(signed(), Ty::I8, &[(CastOp::SExt, Ty::I64)], &ints(&[0, 1]));
    assert_refused_everywhere("sext 2-of-3", &m, &[incomplete("V0 = -1")]);
    // A ZEXT of the signed repr maps -1 to 255 (the mis-widening the bridge
    // documents), so a case spelled -1 names no discriminant AT THE SELECTOR
    // and V0 is uncovered — exactly what the machine does.
    let m = widened_switch_module(
        signed(),
        Ty::I8,
        &[(CastOp::ZExt, Ty::I64)],
        &ints(&[-1, 0, 1]),
    );
    assert_refused_everywhere(
        "zext of a signed repr",
        &m,
        &[stray("-1"), incomplete("V0 = -1")],
    );
    let m = widened_switch_module(
        signed(),
        Ty::I8,
        &[(CastOp::ZExt, Ty::I64)],
        &ints(&[255, 0, 1]),
    );
    assert_accepted_everywhere("zext of a signed repr, 255", &m);

    // Equal-width bitcast (u8 -> i8) and a two-step chain (u8 -> u16 -> i64).
    let m = widened_switch_module(
        enum_def(3),
        Ty::U8,
        &[(CastOp::Bitcast, Ty::I8)],
        &ints(&[0, 1]),
    );
    assert_refused_everywhere("bitcast 2-of-3", &m, &[incomplete("V2 = 2")]);
    let m = widened_switch_module(
        enum_def(3),
        Ty::U8,
        &[(CastOp::ZExt, Ty::U16), (CastOp::SExt, Ty::I64)],
        &ints(&[0, 1, 2]),
    );
    assert_accepted_everywhere("zext+sext full", &m);
    let m = widened_switch_module(
        enum_def(3),
        Ty::U8,
        &[(CastOp::ZExt, Ty::U16), (CastOp::SExt, Ty::I64)],
        &ints(&[0, 2, 7]),
    );
    assert_refused_everywhere("zext+sext stray", &m, &[stray("7"), incomplete("V1 = 1")]);
}

/// Review (WS2.6), adversarial: an omitted variant whose field is an enum
/// ALL of whose variants are uninhabited (`enum Void2 { A0(!), A1(u8, !) }`)
/// is itself uninhabited — rustc lets a `match` omit it, and the format's own
/// `Module::variant_is_uninhabited` (WS3.14) already refuses CONSTRUCTING it
/// — but rule 2 used a private, narrower predicate that only knew
/// zero-variant enums, and refused the legitimate module. Still fail-closed:
/// an enum with ONE inhabited variant is inhabited.
#[test]
fn c15_review_exhaustive_flag_all_uninhabited_enum_field() {
    let void2 = |id: u32, fields: Vec<Vec<Ty>>| {
        EnumDef::new(
            EnumId::new(id),
            "Void2",
            fields
                .into_iter()
                .enumerate()
                .map(|(i, fields)| EnumVariant {
                    name: format!("A{i}"),
                    fields,
                    field_names: vec![],
                })
                .collect(),
        )
        .with_repr(EnumTagRepr::U8)
    };
    let inner = Ty::Enum(EnumId::new(1));
    let mut m = switch_module(2, true, false, 1);
    m.enums[0] = enum_with_v2(inner.clone());
    m.add_enum(void2(1, vec![vec![Ty::Never], vec![Ty::U8, Ty::Never]]));
    assert_accepted_everywhere("V2(Void2{A0(!), A1(u8, !)})", &m);

    let mut m = switch_module(2, true, false, 1);
    m.enums[0] = enum_with_v2(inner);
    m.add_enum(void2(1, vec![vec![Ty::Never], vec![Ty::U8]]));
    assert_refused_everywhere(
        "V2(Half{A0(!), A1(u8)})",
        &m,
        &[cases_incomplete(
            "no case for inhabited variant(s) {V2 = 2}, so the default arm is reachable",
        )],
    );
}

/// Positive fixture: two variants, both covered, default `unreachable`, flag
/// set — the documented legitimate shape.
#[test]
fn c15_bydesign_exhaustive_switch_validates_and_runs() {
    let m = switch_module(2, true, false, 1);
    assert_accepted_everywhere("2 baseline", &m);
    assert_eq!(run_program(&m), Ok(11));
}

// ---------------------------------------------------------------------------
// (3) borrow discipline (F-040)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum Bk {
    /// `p: &mut u64; b = borrow_mut p; store 5 -> b; end_borrow b`
    Baseline,
    /// `p: &u64` (shared) borrowed mutably and written.
    MutThroughShared,
    /// The baseline without `end_borrow`.
    NoEnd,
    /// Two live `borrow_mut` of the same place, both written.
    TwoLiveMut,
    /// `end_borrow` twice.
    DoubleEnd,
    /// A store through the borrow AFTER `end_borrow`.
    UseAfterEnd,
}

fn borrow_module(kind: Bk) -> Module {
    let pty = if kind == Bk::MutThroughShared {
        Ty::Ref(Box::new(Ty::U64))
    } else {
        Ty::RefMut(Box::new(Ty::U64))
    };
    let mut mb = ModuleBuilder::new("c15_borrow");
    let sig = mb.add_func_type(vec![pty.clone()], vec![]);
    let mut fb = mb.function("w", sig);
    fb.set_body_gate(gate());
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, pty);
    fb.switch_to_block(entry);
    let b = fb.borrow_mut(p);
    let five = fb.iconst(Ty::U64, 5);
    if kind == Bk::TwoLiveMut {
        let b2 = fb.borrow_mut(p);
        fb.store(Ty::U64, b, five);
        fb.store(Ty::U64, b2, five);
        fb.store(Ty::U64, b, five);
        fb.end_borrow(b2);
        fb.end_borrow(b);
    } else {
        if kind != Bk::UseAfterEnd {
            fb.store(Ty::U64, b, five);
        }
        if kind != Bk::NoEnd {
            fb.end_borrow(b);
        }
        if kind == Bk::DoubleEnd {
            fb.end_borrow(b);
        }
        if kind == Bk::UseAfterEnd {
            fb.store(Ty::U64, b, five);
        }
    }
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Row `verify.c15` 3a and 3g, flipped (closed upstream by WS2.7): mutation
/// through a shared reference is `BorrowMutThroughSharedRef`, and stamping
/// `UniqueBorrow` / `ValidBorrow` on that function does not excuse it.
#[test]
fn c15_borrow_mut_through_a_shared_ref_is_refused() {
    let refused = [ValidationError::BorrowMutThroughSharedRef { block: 0 }];
    assert_refused_everywhere(
        "3a mut through shared",
        &borrow_module(Bk::MutThroughShared),
        &refused,
    );

    let mut claimed = borrow_module(Bk::MutThroughShared);
    claimed.functions[0]
        .proofs
        .push(ProofAnnotation::UniqueBorrow);
    claimed.functions[0]
        .proofs
        .push(ProofAnnotation::ValidBorrow);
    assert_refused_everywhere("3g claims on 3a", &claimed, &refused);
}

/// Row `verify.c15` 3b-3f, RATIFIED-PRODUCER-OBLIGATION (WS2.7, `TRUST.md`
/// item 12): a borrow never ended, two live mutable borrows, a double end, a
/// use after end, and a shared borrow never ended are borrow LIVENESS, which
/// needs a flow-sensitive checker; the format states it as a producer
/// obligation (discharged by rustc for tRust), so these validate by design.
/// Each is structurally well-formed: every `end_borrow` operand is a borrow
/// result and no `borrow_mut` roots at a shared reference.
#[test]
fn c15_ratified_borrow_liveness_is_a_producer_obligation() {
    for (tag, kind) in [
        ("3b no end_borrow", Bk::NoEnd),
        ("3c two live borrow_mut", Bk::TwoLiveMut),
        ("3d double end_borrow", Bk::DoubleEnd),
        ("3e store after end_borrow", Bk::UseAfterEnd),
    ] {
        assert_accepted_everywhere(tag, &borrow_module(kind));
    }

    let mut mb = ModuleBuilder::new("c15_borrow_shared");
    let pty = Ty::Ref(Box::new(Ty::U64));
    let sig = mb.add_func_type(vec![pty.clone()], vec![Ty::U64]);
    let mut fb = mb.function("r", sig);
    fb.set_body_gate(gate());
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, pty);
    fb.switch_to_block(entry);
    let b = fb.borrow(p);
    let v = fb.load(Ty::U64, b);
    fb.ret(vec![v]);
    fb.build();
    assert_accepted_everywhere(
        "3f shared borrow never ended",
        &mb.build().expect("ModuleBuilder::build: test fixture"),
    );
}

/// Positive fixture: a well-nested mutable borrow of a `&mut` parameter.
#[test]
fn c15_bydesign_well_nested_borrow_validates() {
    assert_accepted_everywhere("3 baseline", &borrow_module(Bk::Baseline));
}

// ---------------------------------------------------------------------------
// (4) readnone / readonly on a storing function (F-021)
// ---------------------------------------------------------------------------

fn attrs_module(attrs: Option<FuncAttrs>, pure_claim: bool) -> Module {
    let pty = Ty::RefMut(Box::new(Ty::U64));
    let mut mb = ModuleBuilder::new("c15_attrs");
    let sig = mb.add_func_type(vec![pty.clone()], vec![]);
    let mut fb = mb.function("w", sig);
    fb.set_body_gate(gate());
    if let Some(a) = attrs {
        fb.set_attrs(a);
    }
    if pure_claim {
        fb.add_function_proof(ProofAnnotation::Pure);
    }
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, pty);
    fb.switch_to_block(entry);
    let five = fb.iconst(Ty::U64, 5);
    fb.store(Ty::U64, p, five);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The one `FuncAttrClaimViolated` a storing `w` marked `attr` earns: the
/// `store` in bb0.
fn attr_violation(m: &Module, attr: &'static str) -> ValidationError {
    let errors = validate_module(m);
    assert_eq!(errors.len(), 1, "{attr}: {errors:?}");
    assert!(
        matches!(
            &errors[0],
            ValidationError::FuncAttrClaimViolated { function, attr: a, block: 0, inst }
                if function == "w" && *a == attr && inst.starts_with("store")
        ),
        "{attr}: {errors:?}"
    );
    errors[0].clone()
}

/// Row `verify.c15` 4a/4b, flipped (closed upstream by WS2.7): `readnone` and
/// `readonly` on a body that executes a `Store` through its `&mut` parameter
/// are `FuncAttrClaimViolated` naming the attribute and the store.
#[test]
fn c15_memory_effect_attrs_on_a_storing_body_are_refused() {
    assert_accepted_everywhere("4 baseline", &attrs_module(None, false));
    let readnone = attrs_module(
        Some(FuncAttrs {
            readnone: true,
            ..FuncAttrs::default()
        }),
        false,
    );
    let expected = attr_violation(&readnone, "readnone");
    assert_refused_everywhere("4a readnone", &readnone, &[expected]);
    let readonly = attrs_module(
        Some(FuncAttrs {
            readonly: true,
            ..FuncAttrs::default()
        }),
        false,
    );
    let expected = attr_violation(&readonly, "readonly");
    assert_refused_everywhere("4b readonly", &readonly, &[expected]);
}

/// Row `verify.c15` 4c: a function-level `Pure` annotation on a body that
/// executes a `Store` validates. WS2.7 checks the `FuncAttrs` memory-effect
/// bits only; `Pure` is a claim-style proof annotation (the GPU gates run on
/// the bare claim), so this row stays a ratchet.
#[test]
fn c15_gap_pure_claim_on_a_storing_body() {
    assert_accepted_everywhere("4c Pure", &attrs_module(None, true));
}

// ---------------------------------------------------------------------------
// (5) proof-table consistency (F-018)
// ---------------------------------------------------------------------------

/// `add(a, b) = a + b` with one `ArithmeticSafety` obligation of `status`,
/// scoped to `scope` (default: `add`), an optional SmtProof certificate, and
/// an optional `[NoOverflow, ProofRef(obligation)]` on the add.
fn proof_module(
    status: ProofStatus,
    scope: Option<FuncId>,
    with_cert: bool,
    proof_ref: bool,
) -> Module {
    let mut mb = ModuleBuilder::new("c15_proof");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let fid = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let scope = scope.or(Some(fid));
    let pid = mb
        .add_proof_obligation(|id| {
            let mut o = ProofObligation::new(
                id,
                ObligationKind::ArithmeticSafety,
                status,
                "a+b no overflow",
            );
            o.function = scope;
            o
        })
        .expect("a fresh obligation id");
    let mut fb = mb.function("add", sig);
    fb.set_body_gate(gate());
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let s = if proof_ref {
        fb.binop_proven(
            trust_ir::BinOp::Add,
            Ty::U64,
            a,
            b,
            vec![ProofAnnotation::NoOverflow, ProofAnnotation::ProofRef(pid)],
        )
    } else {
        fb.add(Ty::U64, a, b)
    };
    fb.ret(vec![s]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    if with_cert {
        m.proof_certificates.push(ProofCertificate {
            obligation: pid,
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(b"unsat".to_vec()),
            assurance: None,
        });
    }
    m
}

/// Row `verify.c15` 5a/5b/5e, flipped by WS1.8 (F-018). 5a: an SmtProof
/// certificate on a Pending row still validates everywhere — it is the honest
/// evidence-awaiting-replay carrier, by design. 5b: the same certificate on a
/// FAILED row is refused by exactly `GroundCertificateStatusInconsistent`
/// (revived, Failed-only), in every tier — even under an authority that
/// admits everything. 5e: a Trusted row with no certificate is refused by
/// exactly `TrustedWithoutJustification` (DECIDE 1A); the same row with a
/// non-blank `ProofEvidence::Trusted` certificate validates everywhere.
#[test]
fn c15_flipped_certificate_status_consistency_is_checked() {
    assert_accepted_everywhere(
        "5 baseline",
        &proof_module(ProofStatus::Pending, None, false, false),
    );
    assert_accepted_everywhere(
        "5a cert on Pending",
        &proof_module(ProofStatus::Pending, None, true, false),
    );
    assert_refused_everywhere(
        "5b cert on Failed",
        &proof_module(ProofStatus::Failed, None, true, false),
        &[ValidationError::GroundCertificateStatusInconsistent {
            obligation: 0,
            status: "Failed",
        }],
    );
    assert_refused_everywhere(
        "5e Trusted, no cert",
        &proof_module(ProofStatus::Trusted, None, false, false),
        &[ValidationError::TrustedWithoutJustification { obligation: 0 }],
    );
    let mut attributed = proof_module(ProofStatus::Trusted, None, false, false);
    attributed.proof_certificates.push(ProofCertificate {
        obligation: attributed.proof_obligations[0].id,
        prover: "audit".to_string(),
        evidence: ProofEvidence::Trusted("accepted on faith by the c15 audit".to_string()),
        assurance: None,
    });
    assert_accepted_everywhere("5e' Trusted, attributed", &attributed);
}

/// Row `verify.c15` 5d, flipped (closed upstream by `5a945757`): a dangling
/// `obligation.function` with no site is refused by name.
#[test]
fn c15_flipped_dangling_function_scope_is_refused() {
    let m = proof_module(ProofStatus::Pending, Some(FuncId::new(77)), false, false);
    let errors = validate_module(&m);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::ObligationFunctionScopeUnresolved { .. })),
        "{errors:?}"
    );
}

/// Mutation controls: the stray certificate is INERT (a `ProofRef` to the
/// Pending row carrying it is unresolved even under AdmitAll), a Trusted row
/// is not `ProofRef` currency, and a `site` naming a block the function does
/// not have is refused by the site rule (before `5a945757` the site rule was
/// the only one that resolved an obligation's position at all).
#[test]
fn c15_control_status_gates_authority() {
    let errors = validate_module_with_authority(
        &proof_module(ProofStatus::Pending, None, true, true),
        &AdmitAll,
    );
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::ProofRefUnresolved { .. })),
        "5c: {errors:?}"
    );
    let mut trusted = proof_module(ProofStatus::Trusted, None, false, true);
    trusted.proof_certificates.push(ProofCertificate {
        obligation: trusted.proof_obligations[0].id,
        prover: "audit".to_string(),
        evidence: ProofEvidence::Trusted("accepted on faith by the c15 audit".to_string()),
        assurance: None,
    });
    let errors = validate_module(&trusted);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::ProofRefUnresolved { .. })),
        "5f: {errors:?}"
    );
    assert!(
        !errors
            .iter()
            .any(|e| matches!(e, ValidationError::TrustedWithoutJustification { .. })),
        "5f: the attributed Trusted row is refused for the ProofRef alone: {errors:?}"
    );
    let mut site = proof_module(ProofStatus::Pending, None, false, false);
    let add = site.functions[0].id;
    site.proof_obligations[0].site = Some(ObligationSite::new(add, BlockId::new(9), 0));
    let errors = validate_module(&site);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::ObligationSiteOutOfRange { .. })),
        "5d control: {errors:?}"
    );
}
