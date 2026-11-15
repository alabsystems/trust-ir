// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Whole-function VC integration tests (roadmap item integration-ay-vc):
// schema determinism, end-to-end proved/refuted VCs with counterexample
// back-mapping, fail-closed unsupported surfaces, and B4 obligation
// outcomes. These run the pinned ay solver in-process (the same way the
// per-op integration tests do), so verdicts below are real solver verdicts,
// not emitted-formula shape checks.

#![allow(clippy::disallowed_methods)] // a test drives ay directly; a panic here is a test failure (r11 item 5, crates/trust-ir-ay/clippy.toml)

use ay::ModelValue;
use trust_ir::Module;
use trust_ir::inst::{BinOp, ICmpOp};
use trust_ir::proof::{
    ObligationKind, ProofAnnotation, ProofFormula, ProofObligation, ProofStatus,
};
use trust_ir::ty::{FatPtrKind, Ty};
use trust_ir::value::{FuncId, ProofId, ValueId};
use trust_ir_ay::{
    AYError, Counterexample, VcObligationOutcome, VcSource, VcVerdict, ay_symbol,
    generate_function_vc, verify_function,
};
use trust_ir_build::{AYBatchBuilder, ModuleBuilder, validate_module};

/// `fn checked_div(a: i32, b: i32) -> i32 { assume(b != 0); a / b }` —
/// the divisor is guarded, so the DivNonZero VC must prove.
fn build_checked_div() -> (Module, ValueId) {
    let mut mb = ModuleBuilder::new("checked_div");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("checked_div", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let zero = fb.iconst(Ty::I32, 0);
    let guard = fb.icmp(ICmpOp::Ne, Ty::I32, b, zero);
    fb.assume(guard);
    let quotient = fb.binop_proven(
        BinOp::SDiv,
        Ty::I32,
        a,
        b,
        vec![ProofAnnotation::DivNonZero],
    );
    fb.ret(vec![quotient]);
    fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), b)
}

/// `fn buggy_div(a: i32, b: i32) -> i32 { a / b }` — no guard, so the
/// DivNonZero VC must refute with a `b = 0` counterexample.
fn build_buggy_div() -> (Module, ValueId) {
    let mut mb = ModuleBuilder::new("buggy_div");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("buggy_div", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let quotient = fb.binop_proven(
        BinOp::SDiv,
        Ty::I32,
        a,
        b,
        vec![ProofAnnotation::DivNonZero],
    );
    fb.ret(vec![quotient]);
    fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), b)
}

// ============================================================================
// Schema determinism
// ============================================================================

/// Same module, built twice from scratch: the VC binds the same symbols in
/// the same order and reaches the same verdicts (no map iteration, no
/// addresses, no run-to-run drift).
#[test]
fn schema_determinism_same_module_same_symbols() {
    let (module1, _) = build_checked_div();
    let (module2, _) = build_checked_div();
    assert_eq!(module1, module2, "builder output itself must be stable");

    let vc1 = verify_function(&module1, module1.functions[0].id).unwrap();
    let vc2 = verify_function(&module2, module2.functions[0].id).unwrap();

    assert_eq!(vc1.bindings, vc2.bindings);
    assert_eq!(vc1.conditions, vc2.conditions);
    assert_eq!(vc1.obligations, vc2.obligations);

    // The bindings are exactly the schema names for the two parameters.
    let func = module1.functions[0].id;
    let names: Vec<&str> = vc1.bindings.iter().map(|(_, n)| n.as_str()).collect();
    assert_eq!(
        names,
        [
            ay_symbol(func, vc1.bindings[0].0),
            ay_symbol(func, vc1.bindings[1].0)
        ]
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
    );
}

// ============================================================================
// End-to-end: proved VC
// ============================================================================

/// The guarded division proves: assume(b != 0) makes `b == 0` UNSAT.
#[test]
fn guarded_div_nonzero_vc_proves() {
    let (module, _) = build_checked_div();
    assert!(validate_module(&module).is_empty());

    let vc = verify_function(&module, module.functions[0].id).unwrap();
    assert_eq!(vc.conditions.len(), 1);
    assert_eq!(
        vc.conditions[0].source,
        VcSource::Annotation(ProofAnnotation::DivNonZero)
    );
    assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved);
    assert!(vc.all_proved());
}

/// An `Assert` whose condition is entailed by an `Assume` proves; the VC
/// checks the assert under the accumulated path constraints.
#[test]
fn assert_entailed_by_assume_proves() {
    let mut mb = ModuleBuilder::new("assert_entailed");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("assert_entailed", ft);

    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // assume(x == 7); assert(x != 0);
    let seven = fb.iconst(Ty::I32, 7);
    let is_seven = fb.icmp(ICmpOp::Eq, Ty::I32, x, seven);
    fb.assume(is_seven);
    let zero = fb.iconst(Ty::I32, 0);
    let nonzero = fb.icmp(ICmpOp::Ne, Ty::I32, x, zero);
    fb.assert(nonzero);
    fb.ret(vec![x]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let vc = verify_function(&module, module.functions[0].id).unwrap();
    assert_eq!(vc.conditions.len(), 1);
    assert_eq!(vc.conditions[0].source, VcSource::Assert);
    assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved);
}

/// An `Assume` AFTER an `Assert` must NOT discharge it: conditions are solved
/// at their own program point, under only the PRECEDING path constraints. A
/// producer must not be able to launder a failing assert by restating it as a
/// trailing assume (assume-after-assert laundering).
#[test]
fn assume_after_assert_does_not_discharge_it() {
    let mut mb = ModuleBuilder::new("assume_after_assert");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("assume_after_assert", ft);

    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // assert(x != 0); assume(x != 0);  -- same condition, wrong order.
    let zero = fb.iconst(Ty::I32, 0);
    let nonzero = fb.icmp(ICmpOp::Ne, Ty::I32, x, zero);
    fb.assert(nonzero);
    fb.assume(nonzero);
    fb.ret(vec![x]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let vc = verify_function(&module, module.functions[0].id).unwrap();
    assert_eq!(vc.conditions.len(), 1);
    assert_eq!(vc.conditions[0].source, VcSource::Assert);
    match &vc.conditions[0].verdict {
        VcVerdict::Refuted {
            counterexample: Counterexample::Model(counterexample),
        } => {
            assert!(
                counterexample.iter().any(|(v, _)| *v == x),
                "counterexample should name the unconstrained operand: {counterexample:?}"
            );
        }
        other => panic!("a trailing assume must not discharge the assert: {other:?}"),
    }
    assert!(!vc.all_proved());
}

// ============================================================================
// End-to-end: refuted VC with counterexample back-mapping
// ============================================================================

/// The unguarded division refutes, and the model maps back through the
/// schema to the divisor's `ValueId` with value 0.
#[test]
fn buggy_div_refutes_with_named_counterexample() {
    let (module, b_param) = build_buggy_div();
    let func = module.functions[0].id;

    let vc = verify_function(&module, func).unwrap();
    assert_eq!(vc.conditions.len(), 1);
    assert!(!vc.all_proved());

    let VcVerdict::Refuted {
        counterexample: Counterexample::Model(counterexample),
    } = &vc.conditions[0].verdict
    else {
        panic!(
            "expected Refuted with a consumer-accepted model, got {:?}",
            vc.conditions[0].verdict
        );
    };
    // The counterexample names the divisor ValueId and assigns it 0.
    let (_, divisor_value) = counterexample
        .iter()
        .find(|(value, _)| *value == b_param)
        .expect("counterexample must name the divisor ValueId");
    match divisor_value {
        ModelValue::BitVec { value, width } => {
            assert_eq!(*width, 32);
            assert_eq!(*value, 0.into());
        }
        other => panic!("expected a 32-bit bitvector assignment, got {other:?}"),
    }
    // And the binding table ties that ValueId to its schema symbol.
    let (_, name) = vc
        .bindings
        .iter()
        .find(|(value, _)| *value == b_param)
        .unwrap();
    assert_eq!(*name, ay_symbol(func, b_param));
}

/// A failing `Assert` refutes with the violating input assignment.
#[test]
fn failing_assert_refutes_with_counterexample() {
    let mut mb = ModuleBuilder::new("assert_fails");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let mut fb = mb.function("assert_fails", ft);

    let entry = fb.create_block();
    let flag = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    fb.assert(flag); // nothing guarantees the parameter is true
    fb.ret(vec![flag]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let vc = verify_function(&module, module.functions[0].id).unwrap();
    assert_eq!(vc.conditions.len(), 1);
    let VcVerdict::Refuted {
        counterexample: Counterexample::Model(counterexample),
    } = &vc.conditions[0].verdict
    else {
        panic!(
            "expected Refuted with a consumer-accepted model, got {:?}",
            vc.conditions[0].verdict
        );
    };
    let (_, flag_value) = counterexample
        .iter()
        .find(|(value, _)| *value == flag)
        .expect("counterexample must name the boolean parameter");
    // Bool is schema-sorted as BitVec(1); the violating assignment is 0.
    match flag_value {
        ModelValue::BitVec { value, width } => {
            assert_eq!(*width, 1);
            assert_eq!(*value, 0.into());
        }
        other => panic!("expected a 1-bit bitvector assignment, got {other:?}"),
    }
}

// ============================================================================
// Fail-closed surfaces
// ============================================================================

/// A DataRaceFree-class annotation is surfaced as a structured Unsupported
/// verdict — never dropped, never a false PASS.
#[test]
fn data_race_free_is_structured_unsupported() {
    let mut mb = ModuleBuilder::new("drf");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("drf", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let sum = fb.binop_proven(
        BinOp::Add,
        Ty::I32,
        a,
        b,
        vec![ProofAnnotation::DataRaceFree],
    );
    fb.ret(vec![sum]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let vc = verify_function(&module, module.functions[0].id).unwrap();
    assert_eq!(vc.conditions.len(), 1);
    assert_eq!(
        vc.conditions[0].source,
        VcSource::Annotation(ProofAnnotation::DataRaceFree)
    );
    assert!(matches!(
        vc.conditions[0].verdict,
        VcVerdict::Unsupported { .. }
    ));
    // An unsupported condition can never read as a full pass.
    assert!(!vc.all_proved());
    assert_eq!(vc.unsupported().count(), 1);
}

/// Unsupported instructions abort the WHOLE-FUNCTION walk fail-closed (no
/// havoc). Since WS5.4 (2) the body then gets the strictly weaker sited VC
/// instead of an error; the walk's refusal is kept, typed, in
/// `whole_function_fallback`, and nothing is approximated: with no sited
/// obligation there is no condition at all.
#[test]
fn unsupported_instruction_fails_closed() {
    let mut mb = ModuleBuilder::new("has_call");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let callee_ft = mb.add_func_type(vec![], vec![Ty::I32]);
    // Build the callee first so the call target exists.
    let mut fb = mb.function("callee", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I32, 0);
    fb.ret(vec![zero]);
    fb.build();

    let mut fb = mb.function("caller", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let result = fb.call(FuncId::new(0), vec![]);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let caller = module.functions[1].id;
    let vc = verify_function(&module, caller).unwrap();
    let err = vc
        .whole_function_fallback
        .as_ref()
        .expect("the whole-function walk must refuse the call");
    assert!(matches!(err, AYError::UnsupportedOp(_)));
    assert!(err.to_string().contains("Call"));
    assert!(
        vc.conditions.is_empty(),
        "nothing is havocked into a condition"
    );
}

/// Multi-block control flow is out of the v1 straight-line scope and fails
/// closed rather than being approximated.
#[test]
fn multi_block_function_yields_only_sited_conditions() {
    let mut mb = ModuleBuilder::new("two_blocks");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("two_blocks", ft);

    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    let zero = fb.iconst(Ty::I32, 0);
    fb.ret(vec![zero]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let func = module.functions[0].id;
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::BoundsCheck,
            ProofStatus::Pending,
            "some check in a multi-block body",
        )
        .with_function(func),
    );

    // A multi-block body no longer hard-errors: it gets the SITED VC. But this
    // body has no `ObligationSite` anywhere, so the VC has nothing to encode and
    // the obligation is refused — the whole-body walk is NOT silently applied to
    // a control-flow graph it never analyzed.
    let vc = verify_function(&module, func).unwrap();
    assert!(
        vc.conditions.is_empty(),
        "no sited obligation => no conditions: {:?}",
        vc.conditions
    );
    assert!(
        matches!(
            vc.obligations[0].1,
            VcObligationOutcome::NotDischarged { .. }
        ),
        "a site-less obligation in a multi-block body must never be backed: {:?}",
        vc.obligations[0].1
    );
}

// ============================================================================
// B4-scoped obligations
// ============================================================================

/// A function-scoped obligation with NO `ObligationSite` is never backed by a
/// function-wide "everything proved", and IS refused when the body yields a
/// refuted condition.
///
/// This is the asymmetry that closes the laundering hole: the old rule marked
/// EVERY function-scoped obligation `ProvedByVc` whenever `all_proved` held,
/// with nothing tying an obligation to a condition — so one easy `DivNonZero`
/// backed every unrelated obligation in the function. The success direction now
/// requires a site; the failure direction (conservative, and how a violated
/// `ensures` surfaces) does not.
#[test]
fn siteless_scoped_obligation_is_never_backed_by_a_function_wide_proof() {
    // Proved case: the body's only condition proves, but the obligation carries
    // no site, so it is UNSUPPORTED — not backed.
    let (mut module, _) = build_checked_div();
    let func = module.functions[0].id;
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            "division is nonzero-checked",
        )
        .with_function(func),
    );
    let vc = verify_function(&module, func).unwrap();
    assert!(vc.all_proved(), "the body's DivNonZero condition proves");
    assert!(
        matches!(vc.obligations[0].1, VcObligationOutcome::Unsupported { .. }),
        "a site-less obligation must not inherit an unrelated proof: {:?}",
        vc.obligations[0].1
    );

    // Refuted case: same obligation on the unguarded body.
    let (mut module, _) = build_buggy_div();
    let func = module.functions[0].id;
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            "division is nonzero-checked",
        )
        .with_function(func),
    );
    let vc = verify_function(&module, func).unwrap();
    assert!(matches!(
        vc.obligations[0].1,
        VcObligationOutcome::NotDischarged { .. }
    ));
}

/// The low-level generator must encode the function owned by the supplied
/// module, not a detached function with a colliding `FuncId` from another
/// module.
#[test]
fn generator_rejects_detached_function_with_colliding_id() {
    let (module, _) = build_checked_div();
    let (other_module, _) = build_buggy_div();

    let error = generate_function_vc(&module, &other_module.functions[0])
        .expect_err("a detached function must not be paired with another module");
    assert!(matches!(error, AYError::UnsupportedOp(_)));
    assert!(error.to_string().contains("does not match"));
}

/// Obligations that carry a formula payload fail closed: the adapter has no
/// in-process SMT-LIB bridge, and must not pretend to have asserted them.
#[test]
fn formula_obligation_is_unsupported_not_false_pass() {
    let (mut module, _) = build_checked_div();
    let func = module.functions[0].id;
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "result is positive",
        )
        .with_function(func)
        .with_formula(ProofFormula::smtlib2("(> result 0)", "Bool")),
    );
    let vc = verify_function(&module, func).unwrap();
    assert!(matches!(
        vc.obligations[0].1,
        VcObligationOutcome::Unsupported { .. }
    ));
}

/// Obligations scoped to OTHER functions are not reported (B4 scoping), and
/// unscoped (legacy) obligations are not claimed either.
#[test]
fn only_this_functions_obligations_are_reported() {
    let (mut module, _) = build_checked_div();
    let func = module.functions[0].id;
    module.proof_obligations.push(ProofObligation::new(
        ProofId::new(0),
        ObligationKind::ArithmeticSafety,
        ProofStatus::Pending,
        "unscoped legacy obligation",
    ));
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            "someone else's obligation",
        )
        .with_function(FuncId::new(999)),
    );
    let vc = verify_function(&module, func).unwrap();
    assert!(vc.obligations.is_empty());
}

/// A vacuous body (no encodable conditions) never discharges an obligation.
#[test]
fn vacuous_vc_refuses_obligation_discharge() {
    let mut mb = ModuleBuilder::new("vacuous");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("identity", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let func = module.functions[0].id;
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "no panics",
        )
        .with_function(func),
    );

    let vc = verify_function(&module, func).unwrap();
    assert!(vc.conditions.is_empty());
    assert!(
        vc.all_proved(),
        "vacuously true — which is why discharge is refused"
    );
    assert!(matches!(
        vc.obligations[0].1,
        VcObligationOutcome::NotDischarged { .. }
    ));
}

// ============================================================================
// End-to-end over the real batch-helper body (ay_batch)
// ============================================================================

/// The regenerated `ay_chc_batch_eval` body (no longer a dummy return) is
/// verified end to end: the assumed non-null caller contract discharges all
/// four NotNull access annotations, and the function-level claims that the
/// VC cannot encode are surfaced, not silently passed.
#[test]
fn batch_transition_body_vc_proves_not_null_contract() {
    let mut builder = AYBatchBuilder::new("chc_batch");
    builder.emit_v4_i32_chc_transition();
    let module = builder
        .build()
        .expect("AYBatchBuilder::build: test fixture");
    assert!(validate_module(&module).is_empty());

    let vc = verify_function(&module, module.functions[0].id).unwrap();

    // Four NotNull annotations (2 loads + 2 stores), all proved via the
    // assumed caller contract.
    assert_eq!(vc.conditions.len(), 4);
    for condition in &vc.conditions {
        assert_eq!(
            condition.source,
            VcSource::Annotation(ProofAnnotation::NotNull)
        );
        assert_eq!(condition.verdict, VcVerdict::Proved);
    }
    assert!(vc.all_proved());

    // All 7 params are schema-bound.
    assert_eq!(vc.bindings.len(), 7);

    // The function-level claims (Deterministic/Terminates/NoPanic/NoUndef)
    // are honestly reported as not covered by this VC; the memory-role hint
    // and descriptive custom tags carry no obligation and are not listed.
    let claims: Vec<&ProofAnnotation> = vc
        .unsupported_function_proofs
        .iter()
        .map(|(a, _)| a)
        .collect();
    assert!(claims.contains(&&ProofAnnotation::Deterministic));
    assert!(claims.contains(&&ProofAnnotation::Terminates));
    assert!(claims.contains(&&ProofAnnotation::NoPanic));
    assert!(claims.contains(&&ProofAnnotation::NoUndef));
    assert!(!claims.contains(&&ProofAnnotation::AppendOnlyBuffer));
    assert_eq!(vc.unsupported_function_proofs.len(), 4);
}

/// Same end-to-end check for the <2 x i64> variant.
#[test]
fn batch_v2_i64_transition_body_vc_proves() {
    let mut builder = AYBatchBuilder::new("chc_batch_v2");
    builder.emit_v2_i64_chc_transition();
    let module = builder
        .build()
        .expect("AYBatchBuilder::build: test fixture");

    let vc = verify_function(&module, module.functions[0].id).unwrap();
    assert_eq!(vc.conditions.len(), 4);
    assert!(vc.all_proved());
}

// ============================================================================
// v34 sited VC: obligation <-> condition binding, and the laundering guard
// ============================================================================

/// Build `fn sited(a: i32) -> i32` whose entry block ends in a LOWERED ASSERT:
/// `condbr (k <u limit), ok, panic_arm` with `panic_arm` ending `unreachable`.
/// `k`/`limit` are constants, so the check is either trivially true or trivially
/// false depending on `k`. Returns the module plus the site of the `condbr`.
fn build_lowered_assert(k: i128, limit: i128) -> (Module, trust_ir::ObligationSite) {
    use trust_ir::value::BlockId;
    let mut mb = ModuleBuilder::new("sited");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let fid = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("sited", ft);
    let entry = fb.create_block();
    let ok = fb.create_block();
    let panic_arm = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let kv = fb.iconst(Ty::U64, k);
    let lv = fb.iconst(Ty::U64, limit);
    let cond = fb.icmp(ICmpOp::Ult, Ty::U64, kv, lv);
    fb.condbr(cond, ok, vec![], panic_arm, vec![]);
    let (block, index) = fb
        .last_emitted_position()
        .expect("the condbr was just emitted");
    fb.switch_to_block(ok);
    fb.ret(vec![a]);
    fb.switch_to_block(panic_arm);
    fb.unreachable();
    fb.build();
    let _ = entry;
    let _ = BlockId::new(0);
    (
        mb.build().expect("ModuleBuilder::build: test fixture"),
        trust_ir::ObligationSite::new(fid, block, index),
    )
}

/// A lowered assert whose condition is NOT constant-foldable: `(x & 15) <u 16`
/// over a free block parameter of the requested integer type.
///
/// `build_lowered_assert` compares two CONSTANTS, so ay's term constructor folds
/// the negated goal to the literal `false` before `check_sat` runs and the
/// resulting bundle proves `false |- _|_` — valid, replayable, and completely
/// uninformative about the program (see the vacuity gate in
/// `vc::capture_replay_evidence`). This builder forces the solver to do real
/// bit-level work, so a `Proved` verdict here is backed by a bundle that
/// actually witnesses the property.
fn build_symbolic_lowered_assert(ty: Ty) -> (Module, trust_ir::ObligationSite) {
    let mut mb = ModuleBuilder::new("sited_symbolic");
    // The entry block's params ARE the signature, so `x` must appear in it.
    let ft = mb.add_func_type(vec![Ty::I32, ty.clone()], vec![Ty::I32]);
    let fid = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("sited_symbolic", ft);
    let entry = fb.create_block();
    let ok = fb.create_block();
    let panic_arm = fb.create_block();
    let ret = fb.add_block_param(entry, Ty::I32);
    // The free symbol the proof must quantify over.
    let x = fb.add_block_param(entry, ty.clone());
    fb.switch_to_block(entry);
    let mask = fb.iconst(ty.clone(), 15);
    let masked = fb.binop(trust_ir::inst::BinOp::And, ty.clone(), x, mask);
    let sixteen = fb.iconst(ty.clone(), 16);
    let cond = fb.icmp(ICmpOp::Ult, ty, masked, sixteen);
    fb.condbr(cond, ok, vec![], panic_arm, vec![]);
    let (block, index) = fb
        .last_emitted_position()
        .expect("the condbr was just emitted");
    fb.switch_to_block(ok);
    fb.ret(vec![ret]);
    fb.switch_to_block(panic_arm);
    fb.unreachable();
    fb.build();
    let _ = entry;
    (
        mb.build().expect("ModuleBuilder::build: test fixture"),
        trust_ir::ObligationSite::new(fid, block, index),
    )
}

fn push_sited(
    module: &mut Module,
    id: u32,
    kind: ObligationKind,
    site: trust_ir::ObligationSite,
) -> ProofId {
    let pid = ProofId::new(id);
    module.proof_obligations.push(
        ProofObligation::new(pid, kind, ProofStatus::Pending, "sited check")
            .with_function(site.function)
            .with_site(site),
    );
    pid
}

/// A CONSTANT-folded assert is still `Proved`, but carries NO evidence: the
/// vacuity gate refuses the bundle because its goal canonicalises to `false`.
///
/// This is the regression pin for the "45 certificates that all prove
/// `false |- _|_`" defect. ay's term constructor folds `not(not(3 <u 10))` to a
/// literal before `check_sat` runs, so the bundle's sole assumption is a
/// constant and replaying it re-establishes nothing about the program. It
/// replays perfectly with `trust_count == 0`, which is exactly what makes it
/// dangerous: a downstream gate counting zero-trust bundles would score it as a
/// real proof.
#[test]
fn constant_folded_assert_is_proved_but_carries_no_vacuous_evidence() {
    let (mut module, site) = build_lowered_assert(3, 10);
    let pid = push_sited(&mut module, 0, ObligationKind::BoundsCheck, site);
    assert!(validate_module(&module).is_empty());

    let vc = verify_function(&module, site.function).unwrap();
    assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved);
    assert!(
        vc.conditions[0].evidence.is_none(),
        "a goal that folds to a constant must NOT yield an attached certificate: \
         the term builder did the reasoning, not the checkable proof"
    );
    // Still no status minted, and still bound to exactly this obligation.
    assert_eq!(vc.obligations, vec![(pid, VcObligationOutcome::ProvedByVc)]);
    let mut module = module;
    let transitions = trust_ir_ay::vc::apply_vc_outcomes(&mut module, &vc).unwrap();
    assert!(transitions.is_empty());
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);
}

/// A sited obligation over a lowered assert with a FREE SYMBOL is proved by AY
/// and now carries a symbolic bundle that independently replays with zero trust
/// steps.
///
/// The bundle is useful evidence but is not yet discharge authority: this
/// generic solver path carries the producer's canonical goal label, while the
/// validator does not independently re-derive that goal from the live IR and
/// compare it with the replayed proof. The separate `BvBlastAuthority` lane has
/// that binding; this generic bundle lane therefore remains `Pending`.
#[test]
fn symbolic_bundle_replays_but_stays_pending_without_goal_binding() {
    // Keep this proof-producing fixture inside AY's bounded strict-checker
    // envelope. It is still genuinely symbolic: no term constructor can fold
    // `(x & 15) < 16` for an unconstrained `x: u8`.
    let (mut module, site) = build_symbolic_lowered_assert(Ty::U8);
    let pid = push_sited(&mut module, 0, ObligationKind::BoundsCheck, site);
    assert!(
        validate_module(&module).is_empty(),
        "the sited module must validate: {:?}",
        validate_module(&module)
    );

    let vc = verify_function(&module, site.function).unwrap();
    assert_eq!(vc.conditions.len(), 1, "one sited condition");
    assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved);
    assert!(matches!(
        vc.conditions[0].source,
        VcSource::LoweredAssert { expected: true, .. }
    ));
    assert_eq!(
        vc.obligations,
        vec![(pid, VcObligationOutcome::ProvedByVc)],
        "the site binds the proof to exactly this obligation"
    );

    let evidence = vc.conditions[0]
        .evidence
        .as_ref()
        .expect("the symbolic BV bundle must replay at the pinned AY revision");
    assert_eq!(evidence.ay_rev, trust_ir_ay::vc::AY_REV);
    assert_eq!(evidence.bundle_schema, ay::PROOF_BUNDLE_SCHEMA);
    assert_eq!(evidence.trust_count, 0);
    assert!(!evidence.goal_canonical.trim().is_empty());
    assert_eq!(
        trust_ir_ay::vc::replay_bundle_offline(&evidence.bundle_bytes),
        Ok(0)
    );

    // ...and applying the VC still mints NO status.
    let mut module = module;
    let transitions = trust_ir_ay::vc::apply_vc_outcomes(&mut module, &vc).unwrap();
    assert!(
        transitions.is_empty(),
        "a solver proof does not mint a public status"
    );
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);
    assert_eq!(module.obligation_diagnostics.len(), 1);
    assert_eq!(
        module.obligation_diagnostics[0].severity,
        trust_ir::proof::DiagnosticSeverity::Note
    );
    // The diagnostic records exactly what was gained and exactly what is still
    // missing: offline replay succeeded, but live goal binding did not.
    let message = &module.obligation_diagnostics[0].message;
    assert!(
        message.contains("REPLAYED OFFLINE") && message.contains("status stays Pending"),
        "expected the replay-without-authority note, got: {message}"
    );
    assert!(
        message.contains("bind to this obligation's goal"),
        "the residual binding gap must remain explicit: {message}"
    );
}

/// The `u64` width of the symbolic identity, which is the sibling of the test
/// above at the widest lowered integer width.
///
/// HISTORY: until ay 0c053832 this case EXCEEDED ay's mandatory aggregate
/// strict-proof validation envelope, and this test pinned the fail-closed
/// behavior for the resource-bounded lane (`Unknown`, no evidence, obligation
/// pending). The strict-check precharge fixes in that release (metered
/// ArrayRowChain accounting b9f2ba20f1, O(total) arg-free resolution
/// c604ecf9f1, poll throttling 0aad6da973) brought the bundle inside the
/// envelope: ay now returns a CHECKER-ACCEPTED proof for it — verified by
/// probe, `verdict=Proved, evidence_present=true` — so the assertion below
/// records the improved truth. The fail-closed contract itself is unchanged
/// and still enforced by the adapter; what this file has LOST is a live
/// in-envelope-exhaustion instance, and it cannot fabricate one until ay
/// exposes a budget knob. If such a knob appears, reinstate a companion test
/// that pins `Unknown` + no evidence under an artificially small envelope.
#[test]
fn wide_symbolic_bundle_proves_with_checker_accepted_evidence() {
    let (mut module, site) = build_symbolic_lowered_assert(Ty::U64);
    let pid = push_sited(&mut module, 0, ObligationKind::BoundsCheck, site);
    assert!(validate_module(&module).is_empty());

    let vc = verify_function(&module, site.function).unwrap();
    assert_eq!(vc.conditions.len(), 1, "one sited condition");
    assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved);
    assert!(
        vc.conditions[0].evidence.is_some(),
        "a strict-checker-accepted proof must carry its evidence bundle"
    );
    assert_eq!(vc.obligations, vec![(pid, VcObligationOutcome::ProvedByVc)]);

    // Same discharge discipline as every Proved path: evidence is not
    // authority, so no status is minted and the obligation stays pending.
    let transitions = trust_ir_ay::vc::apply_vc_outcomes(&mut module, &vc).unwrap();
    assert!(
        transitions.is_empty(),
        "a solver proof does not mint a public status"
    );
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);
}

/// A statically-FALSE lowered assert is refuted, never proved — and the sited
/// VC still refuses to mint `Failed`, because "not provable from this block
/// alone" is not "the program is wrong".
#[test]
fn sited_obligation_over_a_false_check_is_refuted_and_never_failed() {
    let (mut module, site) = build_lowered_assert(10, 3);
    let pid = push_sited(&mut module, 0, ObligationKind::BoundsCheck, site);
    let vc = verify_function(&module, site.function).unwrap();
    assert!(matches!(
        vc.conditions[0].verdict,
        VcVerdict::Refuted { .. }
    ));
    assert!(vc.conditions[0].evidence.is_none(), "no proof, no payload");
    assert!(matches!(
        vc.obligations[0].1,
        VcObligationOutcome::NotDischarged { .. }
    ));
    let transitions = trust_ir_ay::vc::apply_vc_outcomes(&mut module, &vc).unwrap();
    assert!(
        transitions.is_empty(),
        "a locally-unprovable check must not be reported as a program bug"
    );
    let _ = pid;
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);
}

/// THE LAUNDERING REGRESSION. One proved condition must back exactly the ONE
/// obligation sited at it — never its neighbours.
#[test]
fn one_proved_condition_backs_only_its_own_sited_obligation() {
    let (mut module, site) = build_lowered_assert(3, 10);
    let proved = push_sited(&mut module, 0, ObligationKind::BoundsCheck, site);
    // Four more obligations on the SAME function: one sited at a position with
    // no condition, and three unsited (including a Postcondition — the exact
    // shape the old blanket rule marked backed).
    //
    // The no-condition row is a whole-function `PanicFreedom` sited at the
    // `ok` arm's `Return` — the exit shape WS1.8's kind→instruction table
    // names as legitimate (`obligation_kind_admits_site_instruction`). It used
    // to be a `MemorySafety` row at instruction 0, an `iconst`, which that
    // table refuses as `ObligationSiteKindMismatch` — since 6392983d (WS1.8,
    // 2026-09-22) this test failed at the `validate_module` assertion below,
    // unseen because `trust-ir-ay` is a non-default workspace member. A
    // condition is read only out of the `CondBr` at a site, so the `Return`
    // still has none, which is the point of the row.
    let ok_exit = trust_ir::ObligationSite::new(site.function, trust_ir::value::BlockId::new(1), 0);
    let no_condition = push_sited(&mut module, 1, ObligationKind::PanicFreedom, ok_exit);
    for (i, kind) in [
        ObligationKind::Postcondition,
        ObligationKind::MemorySafety,
        ObligationKind::PanicFreedom,
    ]
    .into_iter()
    .enumerate()
    {
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(2 + i as u32),
                kind,
                ProofStatus::Pending,
                "unsited neighbour",
            )
            .with_function(site.function),
        );
    }
    assert!(validate_module(&module).is_empty());

    let vc = verify_function(&module, site.function).unwrap();
    let backed: Vec<ProofId> = vc
        .obligations
        .iter()
        .filter(|(_, o)| matches!(o, VcObligationOutcome::ProvedByVc))
        .map(|(id, _)| *id)
        .collect();
    assert_eq!(
        backed,
        vec![proved],
        "exactly one obligation may be backed by one condition; got {:?}",
        vc.obligations
    );
    let _ = no_condition;
}

/// A `CondBr` whose two arms are BOTH ordinary control flow is not a lowered
/// assert, and the polarity must not be guessed.
#[test]
fn ambiguous_condbr_at_a_site_is_unsupported_not_guessed() {
    let mut mb = ModuleBuilder::new("ambiguous");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let fid = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut fb = mb.function("ambiguous", ft);
    let entry = fb.create_block();
    let l = fb.create_block();
    let r = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let k = fb.iconst(Ty::U64, 3);
    let lim = fb.iconst(Ty::U64, 10);
    let cond = fb.icmp(ICmpOp::Ult, Ty::U64, k, lim);
    fb.condbr(cond, l, vec![], r, vec![]);
    let (block, index) = fb.last_emitted_position().unwrap();
    fb.switch_to_block(l);
    fb.ret(vec![a]);
    fb.switch_to_block(r);
    fb.ret(vec![a]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let site = trust_ir::ObligationSite::new(fid, block, index);
    push_sited(&mut module, 0, ObligationKind::BoundsCheck, site);

    let vc = verify_function(&module, fid).unwrap();
    assert!(
        matches!(vc.conditions[0].verdict, VcVerdict::Unsupported { .. }),
        "neither arm diverges: {:?}",
        vc.conditions[0].verdict
    );
    assert!(matches!(
        vc.obligations[0].1,
        VcObligationOutcome::Unsupported { .. }
    ));
}

/// A fat borrow in the ay lane is typed at the FAT type (the shared
/// `trust_ir::bridge::borrow_result_ty` rule), so the GEP index width gate —
/// the encoder's ONE consumer of recorded value types — REFUSES the module
/// instead of flowing the fat value through the 64-bit thin-pointer model
/// under a false `ptr`. The fat value enters via `Copy`, the one door a fat
/// value has into this lane today: a fat PARAM refuses earlier at `declare`
/// (no fat sort), and `generate_function_vc` takes any `Module` without
/// requiring the validator, so this route is live.
///
/// MUTATION — revert the `Inst::Borrow` arm's bind to a literal `Ty::Ptr`.
/// NOT NEUTRALISED: the borrow then records 64-bit `ptr`, the index gate
/// passes, the whole-function walk succeeds, `whole_function_fallback` is
/// `None`, and the `expect` panics.
#[test]
fn a_fat_borrow_fails_closed_at_the_gep_index_gate() {
    let fat = Ty::FatPtr(FatPtrKind::Str);
    let mut mb = ModuleBuilder::new("fat_borrow");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let mut fb = mb.function("fat_borrow", ft);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let fat_val = fb.copy(fat.clone(), p);
    let b = fb.borrow(fat_val);
    let _g = fb.gep(Ty::I64, p, vec![b]);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    // WS5.4 (2): the walk's refusal is kept on the sited fallback.
    let vc = verify_function(&module, module.functions[0].id).unwrap();
    let err = vc
        .whole_function_fallback
        .expect("the whole-function walk must refuse the fat value");
    assert!(
        matches!(&err, AYError::UnsupportedType(Ty::FatPtr(_))),
        "expected fail-closed on the fat borrow's recorded type, got {err:?}"
    );
}

/// A borrow of a borrow collapses to the chain root IN WALK ORDER: the
/// straight-line walk records the inner borrow's resolved fat type before
/// the outer borrow reads it, so the outer `BorrowMut` is fat too and the
/// index gate refuses the module.
///
/// MUTATION — make either arm bind `Ty::Ptr` again, or read the operand's
/// DECLARED spelling instead of its recorded type. NOT NEUTRALISED: the
/// outer borrow then records `ptr`, the gate passes, the walk succeeds, and
/// the `expect` on `whole_function_fallback` panics.
#[test]
fn a_fat_borrow_chain_collapses_in_walk_order() {
    let fat = Ty::FatPtr(FatPtrKind::Str);
    let mut mb = ModuleBuilder::new("fat_borrow_chain");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let mut fb = mb.function("fat_borrow_chain", ft);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let fat_val = fb.copy(fat.clone(), p);
    let b1 = fb.borrow(fat_val);
    let b2 = fb.borrow_mut(b1);
    let _g = fb.gep(Ty::I64, p, vec![b2]);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    // WS5.4 (2): the walk's refusal is kept on the sited fallback.
    let vc = verify_function(&module, module.functions[0].id).unwrap();
    let err = vc
        .whole_function_fallback
        .expect("the whole-function walk must refuse the fat value");
    assert!(
        matches!(&err, AYError::UnsupportedType(Ty::FatPtr(_))),
        "expected the chained fat borrow to fail closed, got {err:?}"
    );
}

// ============================================================================
// r11 item 5: ay's panicking methods are never reached from a module
// ============================================================================

/// FAILING-FIRST (the surface is unchanged): an UNVALIDATED, ill-typed body —
/// `add i32` whose lhs is an `i64` value — used to panic INSIDE ay
/// (`sort mismatch in bvadd`, the panicking twin of `try_bvadd`), taking the
/// caller down with it. The adapter now calls the `try_*` twin: a typed
/// `AYError::SolverError`, or a condition that is not `Proved` — never a
/// panic. Mutation check: reverting to `bvadd` panics here.
#[test]
fn an_ill_typed_body_is_refused_not_panicked_inside_ay() {
    let mut mb = ModuleBuilder::new("r11_ill_typed");
    let ft = mb.add_func_type(vec![Ty::I64, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let r = fb.binop_proven(BinOp::Add, Ty::I32, a, b, vec![ProofAnnotation::NoOverflow]);
    fb.ret(vec![r]);
    let id = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify_function(&module, id)
    }))
    .expect("verify_function must not panic inside ay on an ill-typed body");
    match outcome {
        Err(AYError::SolverError(message)) => {
            assert!(message.contains("sort mismatch"), "{message}")
        }
        Ok(vc) => assert!(
            vc.conditions
                .iter()
                .all(|condition| !matches!(condition.verdict, VcVerdict::Proved)),
            "an ill-typed body proves nothing: {:?}",
            vc.conditions
        ),
        Err(other) => panic!("expected a typed solver refusal, got {other:?}"),
    }
}

/// FAILING-FIRST (the surface is unchanged): a 2^21-bit constant
/// (`<65536 x i32>`, twice ay's 2^20-bit API width envelope) reaches the
/// whole-function VC's constant encoder. On origin/main `b8f49083` it
/// panicked INSIDE ay (`invalid argument to bv_const: bitvector width 2097152
/// is outside the supported range 1..=1048576`, measured) — a module path the
/// r11 design had believed unreachable (its probe P6 covered wide PARAMETERS
/// and ops, which ay accepts, not a wide CONSTANT). The adapter now calls
/// `try_bv_const`: ay refuses and the refusal is typed. The width envelope is
/// ay's, stated once there (no constant is copied here); the test also fires
/// if a future pin makes the twin panic or silently accept.
#[test]
fn a_wide_bitvector_constant_is_refused_by_ay_not_panicked() {
    let wide = Ty::Vector(Box::new(Ty::I32), 65536);
    let mut mb = ModuleBuilder::new("r11_wide_const");
    let ft = mb.add_func_type(vec![], vec![wide.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let c = fb.const_value(wide.clone(), trust_ir::Constant::Int(0));
    fb.ret(vec![c]);
    let id = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify_function(&module, id)
    }))
    .expect("a wide constant must not panic inside ay");
    match outcome {
        Err(AYError::SolverError(message)) => {
            assert!(message.contains("width"), "{message}")
        }
        other => panic!("expected ay's typed width refusal, got {other:?}"),
    }
}

#[test]
fn popcount_complement_identity_is_proved_and_wrong_total_refuted() {
    for (total, proved) in [(8, true), (7, false)] {
        let mut mb = ModuleBuilder::new("popcount_identity");
        let sig = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
        let mut fb = mb.function("count", sig);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U8);
        fb.switch_to_block(entry);
        let inverted = fb.unop(trust_ir::UnOp::Not, Ty::U8, x);
        let a = fb.unop(trust_ir::UnOp::CtPop, Ty::U8, x);
        let b = fb.unop(trust_ir::UnOp::CtPop, Ty::U8, inverted);
        let sum = fb.binop(BinOp::Add, Ty::U8, a, b);
        let expected = fb.iconst(Ty::U8, total);
        let equal = fb.icmp(ICmpOp::Eq, Ty::U8, sum, expected);
        fb.assert(equal);
        fb.ret(vec![sum]);
        fb.build();
        let module = mb.build().unwrap();
        assert!(validate_module(&module).is_empty());
        let vc = verify_function(&module, module.functions[0].id).unwrap();
        assert_eq!(vc.conditions.len(), 1);
        if proved {
            assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved);
        } else {
            assert!(matches!(
                vc.conditions[0].verdict,
                VcVerdict::Refuted {
                    counterexample: Counterexample::Model(_)
                }
            ));
        }
    }
}

#[test]
fn vector_unary_vcs_use_each_lane_and_refute_wrong_answers() {
    use trust_ir::{UnOp, inst::CastOp};
    for op in [
        UnOp::Neg,
        UnOp::CtPop,
        UnOp::CtLz,
        UnOp::CtTz,
        UnOp::BitReverse,
    ] {
        let raw = 0x00ff_8001u32;
        let expected = raw
            .to_le_bytes()
            .into_iter()
            .enumerate()
            .fold(0u32, |acc, (i, lane)| {
                let result = match op {
                    UnOp::Neg => lane.wrapping_neg(),
                    UnOp::CtPop => lane.count_ones() as u8,
                    UnOp::CtLz => lane.leading_zeros() as u8,
                    UnOp::CtTz => lane.trailing_zeros() as u8,
                    UnOp::BitReverse => lane.reverse_bits(),
                    _ => unreachable!(),
                };
                acc | (u32::from(result) << (8 * i))
            });
        for wrong in [false, true] {
            let mut mb = ModuleBuilder::new("vector_unary_vc");
            let sig = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
            let mut fb = mb.function("lanes", sig);
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, Ty::U32);
            fb.switch_to_block(entry);
            let input = fb.iconst(Ty::U32, i128::from(raw));
            let pin = fb.icmp(ICmpOp::Eq, Ty::U32, x, input);
            fb.assume(pin);
            let vector = Ty::Vector(Box::new(Ty::U8), 4);
            let packed = fb.cast(CastOp::Bitcast, Ty::U32, vector.clone(), x);
            let result = fb.unop(op, vector.clone(), packed);
            let bits = fb.cast(CastOp::Bitcast, vector, Ty::U32, result);
            let expected = fb.iconst(Ty::U32, i128::from(expected ^ u32::from(wrong)));
            let equal = fb.icmp(ICmpOp::Eq, Ty::U32, bits, expected);
            fb.assert(equal);
            fb.ret(vec![bits]);
            fb.build();
            let module = mb.build().unwrap();
            assert!(validate_module(&module).is_empty());
            let vc = verify_function(&module, module.functions[0].id).unwrap();
            assert_eq!(vc.conditions.len(), 1);
            if wrong {
                assert!(
                    matches!(
                        vc.conditions[0].verdict,
                        VcVerdict::Refuted {
                            counterexample: Counterexample::Model(_)
                        }
                    ),
                    "{op:?}: {:?}",
                    vc.conditions[0].verdict
                );
            } else {
                assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved, "{op:?}");
            }
        }
    }
}

#[test]
fn float_integer_cast_vcs_prove_exact_values_and_refute_wrong_values() {
    use trust_ir::inst::CastOp;
    for source in [Ty::F16, Ty::F32, Ty::F64] {
        for signed in [false, true] {
            for saturating in [false, true] {
                for value in [1.75f64, -1.75, f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
                    if !saturating && (!value.is_finite() || (!signed && value < 0.0)) {
                        continue;
                    }
                    for wrong in [false, true] {
                        let dst = if signed { Ty::I32 } else { Ty::U32 };
                        let op = match (signed, saturating) {
                            (false, false) => CastOp::FPToUI,
                            (true, false) => CastOp::FPToSI,
                            (false, true) => CastOp::FPToUISat,
                            (true, true) => CastOp::FPToSISat,
                        };
                        let mut mb = ModuleBuilder::new("fp_integer_cast");
                        let sig = mb.add_func_type(vec![Ty::U8], vec![dst.clone()]);
                        let mut fb = mb.function("convert", sig);
                        let entry = fb.create_block();
                        let param = fb.add_block_param(entry, Ty::U8);
                        fb.switch_to_block(entry);
                        let seven = fb.iconst(Ty::U8, 7);
                        let pinned = fb.icmp(ICmpOp::Eq, Ty::U8, param, seven);
                        fb.assume(pinned);
                        let input = fb.fconst(source.clone(), value);
                        let converted = fb.cast(op, source.clone(), dst.clone(), input);
                        let want = if signed {
                            i128::from((value as i32) ^ i32::from(wrong))
                        } else {
                            i128::from((value as u32) ^ u32::from(wrong))
                        };
                        let expected = fb.iconst(dst.clone(), want);
                        let equal = fb.icmp(ICmpOp::Eq, dst, converted, expected);
                        fb.assert(equal);
                        fb.ret(vec![converted]);
                        fb.build();
                        let module = mb.build().unwrap();
                        assert!(validate_module(&module).is_empty());
                        let vc = verify_function(&module, module.functions[0].id).unwrap();
                        assert_eq!(vc.conditions.len(), 1);
                        if wrong {
                            assert!(
                                matches!(
                                    vc.conditions[0].verdict,
                                    VcVerdict::Refuted {
                                        counterexample: Counterexample::Model(_)
                                    }
                                ),
                                "{source:?} {op:?} {value:?}: {:?}",
                                vc.conditions[0].verdict
                            );
                        } else {
                            assert_eq!(
                                vc.conditions[0].verdict,
                                VcVerdict::Proved,
                                "{source:?} {op:?} {value:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}

/// Every integer literal carrier reaches the solver without i64 truncation.
/// A symbolic parameter retains a real assumption and a replayable obligation.
#[test]
fn integer_literal_boundaries_prove_and_refute_with_exact_widths() {
    use trust_ir::Constant;
    for (ty, input, expected) in [
        (Ty::U64, Constant::Int(i128::from(u64::MAX)), 0),
        (
            Ty::I64,
            Constant::Int(i128::from(i64::MIN)),
            i128::from(i64::MIN) + 1,
        ),
        (
            Ty::I64,
            Constant::Int(i128::from(i64::MAX)),
            i128::from(i64::MIN),
        ),
        (Ty::U128, Constant::u128(u128::MAX), 0),
        (Ty::I128, Constant::Int(i128::MIN), i128::MIN + 1),
        (Ty::I128, Constant::Int(i128::MAX), i128::MIN),
    ] {
        for wrong in [false, true] {
            let mut mb = ModuleBuilder::new("wide_integer_literal");
            let sig = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
            let mut fb = mb.function("add_one", sig);
            let entry = fb.create_block();
            let param = fb.add_block_param(entry, ty.clone());
            fb.switch_to_block(entry);
            let literal = fb.const_value(ty.clone(), input.clone());
            let pinned = fb.icmp(ICmpOp::Eq, ty.clone(), param, literal);
            fb.assume(pinned);
            let one = fb.iconst(ty.clone(), 1);
            let result = fb.binop(BinOp::Add, ty.clone(), param, one);
            let want = fb.iconst(ty.clone(), expected ^ i128::from(wrong));
            let equal = fb.icmp(ICmpOp::Eq, ty.clone(), result, want);
            fb.assert(equal);
            fb.ret(vec![result]);
            fb.build();
            let module = mb.build().unwrap();
            assert!(validate_module(&module).is_empty());
            let vc = verify_function(&module, module.functions[0].id).unwrap();
            assert!(
                vc.whole_function_fallback.is_none(),
                "{ty}: {:?}",
                vc.whole_function_fallback
            );
            assert_eq!(vc.conditions.len(), 1);
            if wrong {
                let VcVerdict::Refuted {
                    counterexample: Counterexample::Model(model),
                } = &vc.conditions[0].verdict
                else {
                    panic!(
                        "{ty}: expected a consumer-accepted model, got {:?}",
                        vc.conditions[0].verdict
                    );
                };
                let (_, assigned) = model
                    .iter()
                    .find(|(id, _)| *id == param)
                    .expect("model must retain the symbolic parameter");
                let ModelValue::BitVec { value, width } = assigned else {
                    panic!("{ty}: expected a bitvector assignment, got {assigned:?}");
                };
                let bits = if matches!(ty, Ty::U64 | Ty::I64) {
                    64
                } else {
                    128
                };
                assert_eq!(*width, bits);
                let raw = match &input {
                    Constant::Int(n) => {
                        let n = ay::BigInt::from(*n);
                        if n < ay::BigInt::from(0) {
                            n + (ay::BigInt::from(1) << bits)
                        } else {
                            n
                        }
                    }
                    Constant::U128(n) => ay::BigInt::from(*n),
                    _ => unreachable!(),
                };
                assert_eq!(*value, raw, "{ty}: high bits or sign were lost");
                assert!(vc.conditions[0].evidence.is_none());
            } else {
                assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved, "{ty}");
                // Whole-function verdicts currently carry no replay payload.
                assert!(vc.conditions[0].evidence.is_none());
            }
        }
        // The sited route is the API that exports replayable proof evidence.
        let mut mb = ModuleBuilder::new("wide_literal_replay");
        let ft = mb.add_func_type(vec![Ty::I32, ty.clone()], vec![Ty::I32]);
        let fid = mb.peek_next_func_id().unwrap();
        let mut fb = mb.function("masked_wide_literal", ft);
        let entry = fb.create_block();
        let ok = fb.create_block();
        let panic_arm = fb.create_block();
        let ret = fb.add_block_param(entry, Ty::I32);
        let arbitrary = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let literal = fb.const_value(ty.clone(), input);
        let changed = fb.binop(BinOp::Xor, ty.clone(), arbitrary, literal);
        let mask = fb.iconst(ty.clone(), 15);
        let low = fb.binop(BinOp::And, ty.clone(), changed, mask);
        let bound = fb.iconst(ty.clone(), 16);
        let within = fb.icmp(ICmpOp::Ult, ty.clone(), low, bound);
        fb.condbr(within, ok, vec![], panic_arm, vec![]);
        let (block, index) = fb.last_emitted_position().unwrap();
        fb.switch_to_block(ok);
        fb.ret(vec![ret]);
        fb.switch_to_block(panic_arm);
        fb.unreachable();
        fb.build();
        let mut module = mb.build().unwrap();
        let site = trust_ir::ObligationSite::new(fid, block, index);
        push_sited(&mut module, 0, ObligationKind::BoundsCheck, site);
        assert!(validate_module(&module).is_empty());
        let vc = verify_function(&module, fid).unwrap();
        assert_eq!(vc.conditions.len(), 1);
        assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved, "{ty}");
        assert!(
            vc.conditions[0].evidence.is_some(),
            "{ty}: missing checked sited proof"
        );
        let evidence = vc.conditions[0].evidence.as_ref().unwrap();
        assert_eq!(
            trust_ir_ay::vc::replay_bundle_offline(&evidence.bundle_bytes),
            Ok(0)
        );
    }
}

#[test]
fn float_bit_images_do_not_use_the_bv_identity_cast() {
    use trust_ir::inst::CastOp;
    let mut mb = ModuleBuilder::new("nan_bit_image");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("invalid_image_model", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = fb.fconst(Ty::F64, f64::NAN);
    let negated = fb.unop(trust_ir::UnOp::FNeg, Ty::F64, value);
    let original_bits = fb.cast(CastOp::Bitcast, Ty::F64, Ty::U64, value);
    let negated_bits = fb.cast(CastOp::Bitcast, Ty::F64, Ty::U64, negated);
    let same_bits = fb.icmp(ICmpOp::Eq, Ty::U64, original_bits, negated_bits);
    fb.assert(same_bits);
    fb.ret(vec![original_bits]);
    fb.build();
    let module = mb.build().unwrap();
    assert!(validate_module(&module).is_empty());
    let vc = verify_function(&module, module.functions[0].id).unwrap();
    // SMT's single NaN value cannot stand in for the observable sign/payload
    // of an IEEE image. Until that image has its own encoding, refuse it.
    assert!(matches!(
        vc.whole_function_fallback,
        Some(AYError::UnsupportedOp(_))
    ));
    assert!(
        vc.conditions
            .iter()
            .all(|condition| !matches!(condition.verdict, VcVerdict::Proved))
    );
}

#[test]
fn float_literals_refuse_non_floating_type_carriers() {
    for ty in [Ty::Bool, Ty::U64, Ty::I128] {
        let mut mb = ModuleBuilder::new("malformed_float_literal");
        let sig = mb.add_func_type(vec![], vec![ty.clone()]);
        let mut fb = mb.function("invalid", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let result = fb.const_value(ty, trust_ir::Constant::Float(1.75));
        fb.ret(vec![result]);
        fb.build();
        let module = mb.build().unwrap();
        assert!(!validate_module(&module).is_empty());
        let vc = verify_function(&module, module.functions[0].id).unwrap();
        assert!(matches!(
            vc.whole_function_fallback,
            Some(AYError::UnsupportedOp(_))
        ));
    }
}

#[test]
fn u128_literals_require_canonical_typed_carriers() {
    for (ty, value) in [
        (Ty::U128, trust_ir::Constant::U128(0)),
        (Ty::I128, trust_ir::Constant::U128(u128::MAX)),
        (Ty::U64, trust_ir::Constant::U128(u128::MAX)),
    ] {
        let mut mb = ModuleBuilder::new("malformed_u128_literal");
        let sig = mb.add_func_type(vec![], vec![ty.clone()]);
        let mut fb = mb.function("invalid", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let result = fb.const_value(ty, value);
        fb.ret(vec![result]);
        fb.build();
        let module = mb.build().unwrap();
        assert!(!validate_module(&module).is_empty());
        let vc = verify_function(&module, module.functions[0].id).unwrap();
        assert!(matches!(
            vc.whole_function_fallback,
            Some(AYError::UnsupportedOp(_))
        ));
    }
}
