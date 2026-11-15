// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS2.11 — Harness inputs for the Kani lane (F-034), the ratified
//! entry-parameter / tape model (`docs/SPEC_RATIFICATIONS.md` "Harness inputs").
//!
//! * A verification harness is a function named by the verification request,
//!   not by an IR marker; its PARAMETERS are the nondeterministic inputs; an
//!   unbounded stream of `any()` is a `(ptr, len)` tape parameter read through
//!   memory; `Assume` on inputs is the vacuity filter.
//! * The reference interpreter names a false assumption `AssumeViolated`
//!   (still an error, still a refusal — the assumption is a premise of every
//!   proof about the function) so a driver can classify "input outside the
//!   assumed domain" apart from program UB. It says nothing about Lean, whose
//!   executable model runs `Assume` as a no-op for a false condition and a
//!   poison one alike (`docs/ub-numerics-policy.md` §4).
//! * The two havoc markers are placement-checked (`HavocMarkerMisplaced`):
//!   `FreshSymbolicHavoc` only on an `undef` node, `RegionHavocStore` only on
//!   a non-volatile `store` node, neither at function scope — mirroring the
//!   trust-mc consumer's own admission check. A legal placement grants
//!   nothing: the marked `undef` validates and stays OUTSIDE the
//!   lowering-target subset (mutation control).

use trust_ir::inst::{BinOp, ICmpOp, Ordering};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir::{Endianness, Inst, Module, TargetInfo};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    }
}

fn run(
    module: &Module,
    entry: FuncId,
    args: Vec<InterpretValue>,
) -> Result<u128, InterpretErrorCode> {
    match Interpreter::with_module(module).execute_func(entry, args) {
        Ok(outcome) => Ok(outcome.returns[0]
            .as_int()
            .expect("int return")
            .as_unsigned()),
        Err(e) => Err(e.code),
    }
}

fn u64v(v: i128) -> InterpretValue {
    InterpretValue::int(Ty::U64, v).expect("u64 value")
}

/// The positive fixture (b7 `param_as_input`): `harness(a: u64, b: u64)`
/// writes its two inputs onto a two-element tape in memory and drains the
/// tape through a callee `tape_next(tape: ptr, len: u64, idx: u64) -> u64`
/// that reads one element through memory (the `(ptr, len)` tape model).
/// `assume a < 10` is the vacuity filter over the universally quantified `a`.
/// Returns `tape[0] + tape[1]`.
fn harness_with_tape() -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info("harness_inputs", target());
    let u64_ty = mb.add_type(Ty::U64);
    let tape_ty = Ty::Array(u64_ty, 2);
    let next_sig = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64], vec![Ty::U64]);
    let tape_next = {
        let mut fb = mb.function("tape_next", next_sig);
        let entry = fb.create_block();
        let tape = fb.add_block_param(entry, Ty::Ptr);
        let len = fb.add_block_param(entry, Ty::U64);
        let idx = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        // The tape's own precondition: the cursor is inside the tape.
        let in_tape = fb.icmp(ICmpOp::Ult, Ty::U64, idx, len);
        fb.assume(in_tape);
        let slot = fb.gep(Ty::U64, tape, vec![idx]);
        let value = fb.load(Ty::U64, slot);
        fb.ret(vec![value]);
        fb.build()
    };
    let harness_sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let harness = {
        let mut fb = mb.function("harness", harness_sig);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let ten = fb.uconst(Ty::U64, 10);
        let a_in_domain = fb.icmp(ICmpOp::Ult, Ty::U64, a, ten);
        fb.assume(a_in_domain);
        let tape = fb.alloca(tape_ty);
        let zero = fb.uconst(Ty::U64, 0);
        let one = fb.uconst(Ty::U64, 1);
        let two = fb.uconst(Ty::U64, 2);
        let slot0 = fb.gep(Ty::U64, tape, vec![zero]);
        fb.store(Ty::U64, slot0, a);
        let slot1 = fb.gep(Ty::U64, tape, vec![one]);
        fb.store(Ty::U64, slot1, b);
        let first = fb.call(tape_next, vec![tape, two, zero]);
        let second = fb.call(tape_next, vec![tape, two, one]);
        let sum = fb.binop(BinOp::Add, Ty::U64, first, second);
        fb.ret(vec![sum]);
        fb.build()
    };
    (
        mb.build().expect("ModuleBuilder::build: test fixture"),
        harness,
    )
}

#[test]
fn ws2_11_a_parametric_harness_with_a_tape_callee_validates_is_in_subset_and_runs() {
    let (module, harness) = harness_with_tape();
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(
        module.check_conformance_subset(),
        Ok(()),
        "the entry-parameter/tape harness is inside the lowering-target subset"
    );
    // Inputs are the entry parameters: two different assignments, two results.
    assert_eq!(run(&module, harness, vec![u64v(3), u64v(4)]), Ok(7));
    assert_eq!(run(&module, harness, vec![u64v(9), u64v(100)]), Ok(109));
}

#[test]
fn ws2_11_assume_on_an_input_is_a_vacuity_filter_named_assume_violated() {
    let (module, harness) = harness_with_tape();
    // `a = 20` is outside the assumed domain `a < 10`: the named refusal, not
    // generic UB — a driver classifies this input as vacuous, not the program
    // as broken.
    assert_eq!(
        run(&module, harness, vec![u64v(20), u64v(1)]),
        Err(InterpretErrorCode::AssumeViolated)
    );
    assert_eq!(
        InterpretErrorCode::AssumeViolated.as_str(),
        "assume_violated"
    );
    // Negative twin: the same input inside the domain runs.
    assert_eq!(run(&module, harness, vec![u64v(5), u64v(1)]), Ok(6));
}

/// `harness(x: u64) -> u64 { assume x < 10; x & 1 }` — the roadmap's own
/// spelling, without a tape.
#[test]
fn ws2_11_assume_x_lt_10_with_x_20_is_assume_violated_not_generic_ub() {
    let mut mb = ModuleBuilder::new("assume_domain");
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("harness", sig);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let ten = fb.uconst(Ty::U64, 10);
    let lt = fb.icmp(ICmpOp::Ult, Ty::U64, x, ten);
    fb.assume(lt);
    let one = fb.uconst(Ty::U64, 1);
    let out = fb.binop(BinOp::And, Ty::U64, x, one);
    fb.ret(vec![out]);
    let harness = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(validate_module(&module).is_empty());
    assert_eq!(
        run(&module, harness, vec![u64v(20)]),
        Err(InterpretErrorCode::AssumeViolated)
    );
    assert_ne!(
        run(&module, harness, vec![u64v(20)]),
        Err(InterpretErrorCode::UndefinedBehavior)
    );
    assert_eq!(run(&module, harness, vec![u64v(7)]), Ok(1));
}

/// A POISON assume condition is still `UndefinedBehavior` (inspecting poison,
/// `docs/ub-numerics-policy.md` §4), never `AssumeViolated`: the new code
/// names a FALSE condition only.
#[test]
fn ws2_11_a_poison_assume_condition_stays_undefined_behavior() {
    let mut mb = ModuleBuilder::new("assume_poison");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let poison = fb.undef(Ty::Bool);
    fb.assume(poison);
    let one = fb.uconst(Ty::U64, 1);
    fb.ret(vec![one]);
    let f = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(validate_module(&module).is_empty());
    assert_eq!(
        run(&module, f, vec![]),
        Err(InterpretErrorCode::UndefinedBehavior)
    );
}

// ---------------------------------------------------------------------------
// Havoc marker placement
// ---------------------------------------------------------------------------

/// The `HavocMarkerMisplaced` rows of a validation result, as
/// `(marker, location)`. Owned, so a call site may pass a freshly computed
/// result without binding it first.
fn misplaced(errors: &[ValidationError]) -> Vec<(&'static str, String)> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::HavocMarkerMisplaced { marker, location } => {
                Some((*marker, location.clone()))
            }
            _ => None,
        })
        .collect()
}

/// `pick() -> u64 { v = <source>; ret v & 1 }` where `source` is emitted by
/// `body`, which may also stamp the marker.
fn marked_module(body: impl FnOnce(&mut trust_ir_build::FunctionBuilder<'_>)) -> Module {
    let mut mb = ModuleBuilder::new("havoc_placement");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("pick", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    body(&mut fb);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn ws2_11_fresh_symbolic_havoc_on_a_return_is_havoc_marker_misplaced() {
    let module = marked_module(|fb| {
        let five = fb.uconst(Ty::U64, 5);
        fb.ret(vec![five]);
        fb.annotate_last(ProofAnnotation::FreshSymbolicHavoc)
            .expect("return node exists");
    });
    let errors = validate_module(&module);
    let found = misplaced(&errors);
    assert_eq!(found.len(), 1, "{errors:?}");
    assert_eq!(found[0].0, "FreshSymbolicHavoc");
    assert!(
        found[0].1.contains("'pick'") && found[0].1.contains("return"),
        "{found:?}"
    );
    assert_eq!(errors.len(), 1, "exactly the named refusal: {errors:?}");
    // The refusal names the marker and the node in its rendering.
    let rendered = errors[0].to_string();
    assert!(
        rendered.contains("FreshSymbolicHavoc") && rendered.contains("misplaced"),
        "{rendered}"
    );
}

#[test]
fn ws2_11_region_havoc_store_on_a_load_is_havoc_marker_misplaced() {
    let module = marked_module(|fb| {
        let cell = fb.alloca(Ty::U64);
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, cell, five);
        let v = fb.load_proven(Ty::U64, cell, vec![ProofAnnotation::RegionHavocStore]);
        fb.ret(vec![v]);
    });
    let errors = validate_module(&module);
    let found = misplaced(&errors);
    assert_eq!(found.len(), 1, "{errors:?}");
    assert_eq!(found[0].0, "RegionHavocStore");
    assert!(found[0].1.contains("load"), "{found:?}");
    assert_eq!(errors.len(), 1, "{errors:?}");
}

#[test]
fn ws2_11_fresh_symbolic_havoc_in_function_proofs_is_havoc_marker_misplaced() {
    let module = marked_module(|fb| {
        fb.add_function_proof(ProofAnnotation::FreshSymbolicHavoc);
        let v = fb.undef(Ty::U64);
        fb.ret(vec![v]);
    });
    let errors = validate_module(&module);
    let found = misplaced(&errors);
    assert_eq!(found.len(), 1, "{errors:?}");
    assert_eq!(found[0].0, "FreshSymbolicHavoc");
    assert!(found[0].1.contains("function scope"), "{found:?}");
    // The other marker at function scope is refused the same way.
    let module = marked_module(|fb| {
        fb.add_function_proof(ProofAnnotation::RegionHavocStore);
        let v = fb.undef(Ty::U64);
        fb.ret(vec![v]);
    });
    let found = misplaced(&validate_module(&module));
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].0, "RegionHavocStore");
}

/// A VOLATILE store is not a region havoc: the marker describes a bulk write
/// whose region is unbounded, and the memory model treats a volatile store as
/// a single observable access — the trust-mc consumer refuses the pairing,
/// and so does the validator.
#[test]
fn ws2_11_region_havoc_store_on_a_volatile_store_is_havoc_marker_misplaced() {
    let module = marked_module(|fb| {
        let cell = fb.alloca(Ty::U64);
        let five = fb.uconst(Ty::U64, 5);
        fb.store_volatile(Ty::U64, cell, five);
        fb.annotate_last(ProofAnnotation::RegionHavocStore)
            .expect("store node exists");
        let v = fb.load(Ty::U64, cell);
        fb.ret(vec![v]);
    });
    let found = misplaced(&validate_module(&module));
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].0, "RegionHavocStore");
    assert!(found[0].1.contains("store"), "{found:?}");
}

/// The right-reason twins: each marker on the node it describes validates.
/// And the mutation control: the legal `FreshSymbolicHavoc` on `undef` grants
/// nothing — the marked node stays OUTSIDE the lowering-target subset, while
/// the unmarked poison twin is inside it.
#[test]
fn ws2_11_legal_placements_validate_and_the_marker_grants_nothing() {
    let marked = marked_module(|fb| {
        let v = fb.undef_proven(Ty::U64, vec![ProofAnnotation::FreshSymbolicHavoc]);
        fb.ret(vec![v]);
    });
    assert!(validate_module(&marked).is_empty());
    let violations = marked
        .check_conformance_subset()
        .expect_err("the marked undef is outside the subset");
    assert!(
        violations
            .iter()
            .any(|v| v.reason.contains("FreshSymbolicHavoc is not ratified")),
        "{violations:?}"
    );
    let unmarked = marked_module(|fb| {
        let v = fb.undef(Ty::U64);
        fb.ret(vec![v]);
    });
    assert!(validate_module(&unmarked).is_empty());
    assert_eq!(unmarked.check_conformance_subset(), Ok(()));

    let region = marked_module(|fb| {
        let cell = fb.alloca(Ty::U64);
        let five = fb.uconst(Ty::U64, 5);
        fb.store_proven(Ty::U64, cell, five, vec![ProofAnnotation::RegionHavocStore]);
        let v = fb.load(Ty::U64, cell);
        fb.ret(vec![v]);
    });
    let errors = validate_module(&region);
    assert!(errors.is_empty(), "{errors:?}");
    assert!(
        region.functions[0].blocks[0].body.iter().any(|n| matches!(
            n.inst,
            Inst::Store {
                volatile: false,
                ..
            }
        ) && n
            .proofs
            .contains(&ProofAnnotation::RegionHavocStore)),
        "the fixture carries the marker on a non-volatile store"
    );
    assert!(
        region.check_conformance_subset().is_err(),
        "RegionHavocStore is not ratified into the subset either"
    );
}

/// The rule is function-local, so the STANDALONE entry point refuses it too:
/// `validate_function` on a bare `Function` names the same misplacement, and
/// neither path counts it twice (the module walk owns it under module
/// validation).
#[test]
fn ws2_11_validate_function_alone_refuses_a_misplaced_marker() {
    let module = marked_module(|fb| {
        let five = fb.uconst(Ty::U64, 5);
        fb.ret(vec![five]);
        fb.annotate_last(ProofAnnotation::FreshSymbolicHavoc)
            .expect("return node exists");
    });
    let func = &module.functions[0];
    let found = misplaced(&trust_ir_build::validate_function(func));
    assert_eq!(found.len(), 1, "standalone validation refuses it");
    assert_eq!(found[0].0, "FreshSymbolicHavoc");
    // Exactly once under module validation as well.
    assert_eq!(misplaced(&validate_module(&module)).len(), 1);

    // Right-reason twin: the legal placement is accepted on both paths.
    let legal = marked_module(|fb| {
        let v = fb.undef_proven(Ty::U64, vec![ProofAnnotation::FreshSymbolicHavoc]);
        fb.ret(vec![v]);
    });
    assert!(misplaced(&trust_ir_build::validate_function(&legal.functions[0])).is_empty());
    assert!(misplaced(&validate_module(&legal)).is_empty());
}

/// Mutation control for the RULE: a module stamping BOTH markers on legal
/// nodes plus a third on an illegal one is refused exactly once, naming the
/// illegal site — the rule walks every node and every function's proofs and
/// counts nothing twice.
#[test]
fn ws2_11_the_rule_names_exactly_the_misplaced_sites() {
    let mut mb = ModuleBuilder::new("havoc_placement_mixed");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    {
        let mut fb = mb.function("legal", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.undef_proven(Ty::U64, vec![ProofAnnotation::FreshSymbolicHavoc]);
        let cell = fb.alloca(Ty::U64);
        fb.store_proven(Ty::U64, cell, v, vec![ProofAnnotation::RegionHavocStore]);
        fb.ret(vec![v]);
        fb.build();
    }
    {
        let mut fb = mb.function("illegal", sig);
        fb.add_function_proof(ProofAnnotation::RegionHavocStore);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.undef(Ty::U64);
        let cell = fb.alloca(Ty::U64);
        fb.store(Ty::U64, cell, v);
        let r = fb.load_proven(Ty::U64, cell, vec![ProofAnnotation::FreshSymbolicHavoc]);
        fb.ret(vec![r]);
        fb.build();
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut found = misplaced(&validate_module(&module));
    found.sort();
    assert_eq!(found.len(), 2, "{found:?}");
    assert_eq!(found[0].0, "FreshSymbolicHavoc");
    assert!(
        found[0].1.contains("'illegal'") && found[0].1.contains("load"),
        "{found:?}"
    );
    assert_eq!(found[1].0, "RegionHavocStore");
    assert!(
        found[1].1.contains("'illegal'") && found[1].1.contains("function scope"),
        "{found:?}"
    );
}

// ---------------------------------------------------------------------------
// WS2.11 review — adversarial placements the implementer did not write
// ---------------------------------------------------------------------------

/// REVIEW (adversarial): a BODY-LESS declaration carrying a havoc marker at
/// function scope. This is the exact shape the ratification names as NOT an
/// input source (`nondet_u64()`), and it is the one function shape with no
/// blocks at all — a rule that walked only block bodies, or that reached
/// function scope only through a block walk, would accept it silently and
/// hand a consumer a "this declaration yields a fresh unconstrained value"
/// claim the format does not make.
#[test]
fn ws2_11_review_a_bodyless_declaration_carrying_a_marker_is_refused() {
    let mut mb = ModuleBuilder::new("havoc_on_declaration");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let _decl = mb.declare_function("nondet_u64", sig);
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let decl = module
        .functions
        .iter_mut()
        .find(|f| f.name == "nondet_u64")
        .expect("the declaration");
    assert!(decl.blocks.is_empty(), "a declaration has no blocks");
    decl.proofs.push(ProofAnnotation::FreshSymbolicHavoc);

    let found = misplaced(&validate_module(&module));
    assert_eq!(found.len(), 1, "the declaration is refused by name");
    assert_eq!(found[0].0, "FreshSymbolicHavoc");
    assert!(
        found[0].1.contains("nondet_u64") && found[0].1.contains("function scope"),
        "{found:?}"
    );
    // The standalone path refuses it too, and exactly once.
    assert_eq!(
        misplaced(&trust_ir_build::validate_function(
            module
                .functions
                .iter()
                .find(|f| f.name == "nondet_u64")
                .unwrap()
        ))
        .len(),
        1
    );
}

/// REVIEW (adversarial): BOTH markers on ONE node, where the node is legal for
/// exactly one of them. A rule that keyed on "does this node carry a havoc
/// marker at all" would accept the pair (the store is a legal
/// `RegionHavocStore` site); the per-annotation rule must refuse the
/// `FreshSymbolicHavoc` half and only that half.
#[test]
fn ws2_11_review_two_markers_on_one_node_refuse_only_the_misplaced_half() {
    let module = marked_module(|fb| {
        let cell = fb.alloca(Ty::U64);
        let five = fb.uconst(Ty::U64, 5);
        fb.store_proven(
            Ty::U64,
            cell,
            five,
            vec![
                ProofAnnotation::RegionHavocStore,
                ProofAnnotation::FreshSymbolicHavoc,
            ],
        );
        let v = fb.load(Ty::U64, cell);
        fb.ret(vec![v]);
    });
    let errors = validate_module(&module);
    let found = misplaced(&errors);
    assert_eq!(found.len(), 1, "exactly the misplaced half: {errors:?}");
    assert_eq!(found[0].0, "FreshSymbolicHavoc");
    assert!(found[0].1.contains("store"), "{found:?}");
}

/// REVIEW (adversarial): `RegionHavocStore` on an `AtomicStore`. "Store" in
/// the ratification means `Inst::Store`, not every store-like opcode: an
/// atomic store is a single, ordered, observable access, and a consumer that
/// read the marker there would havoc a region around a synchronising write.
/// The narrowness is the point, so it is pinned.
#[test]
fn ws2_11_review_region_havoc_store_on_an_atomic_store_is_misplaced() {
    let module = marked_module(|fb| {
        let cell = fb.alloca(Ty::U64);
        let five = fb.uconst(Ty::U64, 5);
        fb.atomic_store(Ty::U64, cell, five, Ordering::SeqCst);
        fb.annotate_last(ProofAnnotation::RegionHavocStore)
            .expect("atomic store node exists");
        let v = fb.load(Ty::U64, cell);
        fb.ret(vec![v]);
    });
    let found = misplaced(&validate_module(&module));
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].0, "RegionHavocStore");
    // Right-reason twin: the SAME marker on the plain store of the same cell
    // validates, so the refusal is about the opcode, not the pointer.
    let legal = marked_module(|fb| {
        let cell = fb.alloca(Ty::U64);
        let five = fb.uconst(Ty::U64, 5);
        fb.store_proven(Ty::U64, cell, five, vec![ProofAnnotation::RegionHavocStore]);
        let v = fb.load(Ty::U64, cell);
        fb.ret(vec![v]);
    });
    assert!(misplaced(&validate_module(&legal)).is_empty());
}

/// REVIEW (adversarial): a misplaced marker hidden in a NON-entry block. The
/// location must name that block, and the refusal must not depend on the
/// entry block. A producer hiding the claim one branch deep gets the same
/// named refusal.
#[test]
fn ws2_11_review_a_misplaced_marker_in_a_non_entry_block_is_refused_by_location() {
    let mut mb = ModuleBuilder::new("havoc_deep");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("pick", sig);
    let entry = fb.create_block();
    let tail = fb.create_block();
    fb.switch_to_block(entry);
    fb.br(tail, vec![]);
    fb.switch_to_block(tail);
    let five = fb.uconst(Ty::U64, 5);
    fb.annotate_last(ProofAnnotation::FreshSymbolicHavoc)
        .expect("const node exists");
    fb.ret(vec![five]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let found = misplaced(&validate_module(&module));
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].0, "FreshSymbolicHavoc");
    assert!(
        found[0].1.contains("bb1") && found[0].1.contains("const"),
        "the location names the block it was hidden in: {found:?}"
    );
}

/// REVIEW (adversarial): the CODEGEN-grade entry point must refuse it too.
/// `validate_module_for_codegen` is the gate a backend consults, and it runs a
/// different `ValidationConfig`; a rule wired only into the default pass would
/// let the misplaced claim through the one door that matters for emission.
#[test]
fn ws2_11_review_the_codegen_grade_entry_point_refuses_a_misplaced_marker() {
    let module = marked_module(|fb| {
        let five = fb.uconst(Ty::U64, 5);
        fb.ret(vec![five]);
        fb.annotate_last(ProofAnnotation::FreshSymbolicHavoc)
            .expect("return node exists");
    });
    let found = misplaced(&trust_ir_build::validate_module_for_codegen(&module));
    assert_eq!(found.len(), 1, "the codegen gate names it too");
    assert_eq!(found[0].0, "FreshSymbolicHavoc");
    // Right-reason twin: the legal placement passes the same gate.
    let legal = marked_module(|fb| {
        let v = fb.undef_proven(Ty::U64, vec![ProofAnnotation::FreshSymbolicHavoc]);
        fb.ret(vec![v]);
    });
    assert!(misplaced(&trust_ir_build::validate_module_for_codegen(&legal)).is_empty());
}
