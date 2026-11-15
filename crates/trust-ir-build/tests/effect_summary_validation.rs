// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS1.14 (F-013): typed effect summaries and world epochs, VALIDATED.
//!
//! `FunctionSummary.effects` is the frame half of a contract: the memory a
//! call may read and write, and whether it allocates, frees, unwinds or
//! performs I/O. On a DEFINITION the validator checks the claim against the
//! body with a sound, syntactic over-approximation and refuses an uncovered
//! effect as `EffectSummaryViolated`; on a body-less DECLARATION it is a claim
//! a caller may rely on only once `validate_linked_module` authenticated the
//! declaration's `backed_by` (far effects restated exactly). The world epochs
//! `WorldPre` / `WorldPost` replace the legacy un-epoched `World`, which is
//! unbindable on a `proved` summary.
//!
//! Every positive below has its negative twin refused by the SPECIFIC named
//! reason, and the mutation control shows the refusal is about the body, not
//! the summary: removing the store makes the tighter summary valid. The
//! proof-program rows F-013 closes are ported as tests named after them.

use std::collections::BTreeSet;

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;
use trust_ir::inst::CastOp;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofCertificate, ProofFormula,
    ProofObligation, ProofStatus, RejectingModuleProofAuthority,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, GlobalId, ProofId};
use trust_ir::{
    Constant, EffectPlace, EffectSet, EffectSummary, Endianness, ExternRef, Function,
    FunctionSummary, Global, Linkage, Module, ModuleImport, Producer, TargetInfo,
};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, ValidationError, validate_linked_module, validate_module,
};

// ---------------------------------------------------------------------------
// fixtures
// ---------------------------------------------------------------------------

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn ptr() -> Ty {
    Ty::PtrMut(Box::new(Ty::U64))
}

fn p(index: u32) -> EffectPlace {
    EffectPlace::ParamPointee { index }
}

fn writes(places: &[EffectPlace]) -> EffectSummary {
    EffectSummary::pure().writing(EffectSet::of(places.iter().copied()))
}

fn with_effects(effects: EffectSummary) -> FunctionSummary {
    FunctionSummary::new().with_effects(effects)
}

/// `fn set(p: *mut u64, q: *mut u64) { *<target> = 7 }`, where `store`
/// picks the address from `(p, q)`; `None` emits no store at all.
fn setter(
    store: Option<
        fn(trust_ir::value::ValueId, trust_ir::value::ValueId) -> trust_ir::value::ValueId,
    >,
    effects: EffectSummary,
) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("setter", target());
    let ft = mb.add_func_type(vec![ptr(), ptr()], vec![]);
    let mut fb = mb.function("set", ft);
    let entry = fb.create_block();
    let pp = fb.add_block_param(entry, ptr());
    let qq = fb.add_block_param(entry, ptr());
    fb.switch_to_block(entry);
    if let Some(pick) = store {
        let seven = fb.uconst(Ty::U64, 7);
        fb.store(Ty::U64, pick(pp, qq), seven);
    }
    fb.ret(vec![]);
    fb.set_summary(with_effects(effects));
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn first(p: trust_ir::value::ValueId, _: trust_ir::value::ValueId) -> trust_ir::value::ValueId {
    p
}

fn second(_: trust_ir::value::ValueId, q: trust_ir::value::ValueId) -> trust_ir::value::ValueId {
    q
}

/// The `(function, effect)` pairs of every `EffectSummaryViolated`, and
/// whether ANY other error is present (it must not be, for a named twin).
fn violations(errors: &[ValidationError]) -> BTreeSet<(String, &'static str)> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::EffectSummaryViolated {
                function, effect, ..
            } => Some((function.clone(), *effect)),
            _ => None,
        })
        .collect()
}

fn only_effect_violations(errors: &[ValidationError]) -> bool {
    errors
        .iter()
        .all(|e| matches!(e, ValidationError::EffectSummaryViolated { .. }))
}

fn violation_text(errors: &[ValidationError], effect: &str) -> String {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::EffectSummaryViolated {
                effect: named,
                inst,
                ..
            } if *named == effect => Some(inst.clone()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join(" | ")
}

fn assert_clean(module: &Module) {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "expected a valid module: {errors:#?}");
}

fn summary_errors(errors: &[ValidationError]) -> Vec<String> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::InvalidFunctionSummary { detail, .. } => Some(detail.clone()),
            _ => None,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// positives
// ---------------------------------------------------------------------------

/// A pure function with `Nothing` / `Nothing` and every flag false.
#[test]
fn a_pure_function_validates_with_the_pure_summary() {
    let mut mb = ModuleBuilder::new_with_target_info("pure", target());
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("add", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    let y = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    // A local alloca is invisible to the caller: no coverage needed.
    let slot = fb.alloca(Ty::U64);
    fb.store(Ty::U64, slot, x);
    let back = fb.load(Ty::U64, slot);
    let sum = fb.add(Ty::U64, back, y);
    fb.ret(vec![sum]);
    fb.set_summary(with_effects(EffectSummary::pure()));
    fb.build();
    assert_clean(&mb.build().expect("ModuleBuilder::build: test fixture"));
}

/// A writer through `&mut` parameter 0 with `writes: Places([ParamPointee 0])`.
#[test]
fn a_writer_through_param_zero_validates_with_that_place() {
    assert_clean(&setter(Some(first), writes(&[p(0)])));
}

// ---------------------------------------------------------------------------
// negative twins, each refused by name
// ---------------------------------------------------------------------------

/// Twin: the store goes through parameter 1, which the summary does not list.
#[test]
fn a_store_through_an_unlisted_param_is_refused() {
    let errors = validate_module(&setter(Some(second), writes(&[p(0)])));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("set".to_string(), "writes")]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    assert!(
        violation_text(&errors, "writes").contains("*param1"),
        "the refusal names the uncovered place: {errors:#?}"
    );
}

/// Twin: a store through an `IntToPtr` address with no `Everything`.
#[test]
fn a_store_through_inttoptr_needs_everything() {
    let build = |effects: EffectSummary| {
        let mut mb = ModuleBuilder::new_with_target_info("forged", target());
        let ft = mb.add_func_type(vec![ptr(), Ty::U64], vec![]);
        let mut fb = mb.function("forge", ft);
        let entry = fb.create_block();
        let _p = fb.add_block_param(entry, ptr());
        let a = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        // `IntToPtr` yields the thin opaque `Ptr` (the validator's cast rule).
        let forged = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, a);
        let one = fb.uconst(Ty::U64, 1);
        fb.store(Ty::U64, forged, one);
        fb.ret(vec![]);
        fb.set_summary(with_effects(effects));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let errors = validate_module(&build(writes(&[p(0)])));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("forge".to_string(), "writes")]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    assert!(
        violation_text(&errors, "writes").contains("Everything"),
        "{errors:#?}"
    );
    // Control: the honest summary admits it.
    assert_clean(&build(EffectSummary::pure().writing(EffectSet::Everything)));
}

/// `fn caller(p, q)` calling `callee(arg)`; the callee is built by `callee`.
fn caller_module(
    callee_summary: Option<FunctionSummary>,
    callee_is_declaration: bool,
    pass_second: bool,
    caller_effects: EffectSummary,
) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("calls", target());
    let callee_ty = mb.add_func_type(vec![ptr()], vec![]);
    let callee = if callee_is_declaration {
        mb.declare_function("callee", callee_ty)
    } else {
        let mut fb = mb.function("callee", callee_ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, ptr());
        fb.switch_to_block(entry);
        let v = fb.uconst(Ty::U64, 3);
        fb.store(Ty::U64, a, v);
        fb.ret(vec![]);
        fb.build()
    };
    let caller_ty = mb.add_func_type(vec![ptr(), ptr()], vec![]);
    let mut fb = mb.function("caller", caller_ty);
    let entry = fb.create_block();
    let pp = fb.add_block_param(entry, ptr());
    let qq = fb.add_block_param(entry, ptr());
    fb.switch_to_block(entry);
    fb.call_void(callee, vec![if pass_second { qq } else { pp }]);
    fb.ret(vec![]);
    fb.set_summary(with_effects(caller_effects));
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let slot = module
        .functions
        .iter()
        .position(|f| f.id == callee)
        .expect("callee");
    module.functions[slot].summary = callee_summary;
    module
}

/// Twin: a call to a callee with NO summary, without `Everything`.
#[test]
fn an_unsummarized_call_needs_the_top_summary() {
    let errors = validate_module(&caller_module(None, false, false, writes(&[p(0)])));
    let named = violations(&errors);
    assert!(
        named.contains(&("caller".to_string(), "writes"))
            && named.contains(&("caller".to_string(), "reads"))
            && named.contains(&("caller".to_string(), "io")),
        "an unsummarized callee is havoc on both sides and may do I/O: {errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    assert!(
        violation_text(&errors, "writes").contains("no admissible effect summary"),
        "{errors:#?}"
    );
    // Control: the top summary admits it.
    assert_clean(&caller_module(None, false, false, EffectSummary::top()));
}

/// Twin: a LOAD through parameter 1 with `reads: Nothing`.
#[test]
fn a_load_through_an_unlisted_param_is_refused() {
    let build = |reads: EffectSet| {
        let mut mb = ModuleBuilder::new_with_target_info("reader", target());
        let ft = mb.add_func_type(vec![ptr(), ptr()], vec![Ty::U64]);
        let mut fb = mb.function("read", ft);
        let entry = fb.create_block();
        let _p = fb.add_block_param(entry, ptr());
        let q = fb.add_block_param(entry, ptr());
        fb.switch_to_block(entry);
        let v = fb.load(Ty::U64, q);
        fb.ret(vec![v]);
        fb.set_summary(with_effects(EffectSummary::pure().reading(reads)));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let errors = validate_module(&build(EffectSet::Nothing));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("read".to_string(), "reads")]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    assert!(
        violation_text(&errors, "reads").contains("*param1"),
        "{errors:#?}"
    );
    // Control: listing the place admits it.
    assert_clean(&build(EffectSet::of([p(1)])));
}

/// Twin: a summarized callee writes its `ParamPointee 0`; the caller passes
/// ITS parameter 1, so the write lands on the caller's `*param1` — which the
/// caller does not list.
#[test]
fn a_callee_write_maps_through_the_argument() {
    let callee = Some(with_effects(writes(&[p(0)])));
    let errors = validate_module(&caller_module(callee.clone(), false, true, writes(&[p(0)])));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("caller".to_string(), "writes")]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    assert!(
        violation_text(&errors, "writes").contains("*param1"),
        "{errors:#?}"
    );
    // Control: passing parameter 0 instead lands inside the caller's summary.
    assert_clean(&caller_module(callee, false, false, writes(&[p(0)])));
}

/// Twin: a body-less declaration claims `effects: pure`, and nothing
/// authenticates it — so the caller may NOT use it to keep its own `writes`
/// tight: it is havoc.
#[test]
fn an_unauthenticated_declaration_summary_is_havoc() {
    let claimed = Some(with_effects(EffectSummary::pure()));
    let errors = validate_module(&caller_module(
        claimed.clone(),
        true,
        false,
        EffectSummary::pure(),
    ));
    let named = violations(&errors);
    assert!(
        named.contains(&("caller".to_string(), "writes"))
            && named.contains(&("caller".to_string(), "io")),
        "a declaration's effects are a claim with no body: {errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    // Control: the same callee DEFINED with a pure body is admissible, so the
    // refusal is about authentication, not the claim's text.
    let mut defined = caller_module(claimed, false, false, EffectSummary::pure());
    let body = &mut defined.functions[0].blocks[0].body;
    body.retain(|node| !matches!(node.inst, trust_ir::inst::Inst::Store { .. }));
    assert_clean(&defined);
}

/// Twin: a DEFINED callee whose linkage is interposable (`Weak`) may be
/// replaced by another body at link time, so its summary is not admissible:
/// the call is havoc. Control: the same callee with `WeakOdr` (the disclosed
/// one-definition-rule premise) is admissible.
#[test]
fn an_interposable_callee_summary_is_havoc() {
    let build = |linkage: Linkage| {
        let mut m = caller_module(
            Some(with_effects(writes(&[p(0)]))),
            false,
            false,
            writes(&[p(0)]),
        );
        let slot = m
            .functions
            .iter()
            .position(|f| f.name == "callee")
            .expect("callee");
        m.functions[slot].linkage = linkage;
        m
    };
    let errors = validate_module(&build(Linkage::Weak));
    assert!(
        violations(&errors).contains(&("caller".to_string(), "writes")),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    assert_clean(&build(Linkage::WeakOdr));
}

// ---------------------------------------------------------------------------
// the mutation control
// ---------------------------------------------------------------------------

/// The tighter summary is refused WITH the store and valid WITHOUT it: the
/// rule reads the body, not the summary.
#[test]
fn removing_the_store_makes_the_tighter_summary_valid() {
    let errors = validate_module(&setter(Some(first), EffectSummary::pure()));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("set".to_string(), "writes")]),
        "{errors:#?}"
    );
    assert_clean(&setter(None, EffectSummary::pure()));
}

// ---------------------------------------------------------------------------
// the rest of the body rules
// ---------------------------------------------------------------------------

/// A `GlobalAddr` store needs that global; a `Select` of a parameter and an
/// alloca needs the parameter (both arms are traced); a heap allocation and a
/// free each need their flag (`Invoke` / `Resume` and a callee's flags:
/// `invoke_and_resume_need_may_unwind`, `a_callee_passes_its_flags_on`).
#[test]
fn globals_selects_and_flags_are_attributed() {
    let build = |effects: EffectSummary| {
        let mut mb = ModuleBuilder::new_with_target_info("mixed", target());
        mb.add_global(Global {
            name: "COUNTER".into(),
            ty: Ty::U64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let ft = mb.add_func_type(vec![ptr(), Ty::Bool], vec![]);
        let mut fb = mb.function("mixed", ft);
        let entry = fb.create_block();
        let pp = fb.add_block_param(entry, ptr());
        let c = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        let g = fb.global_addr(GlobalId::new(0));
        let one = fb.uconst(Ty::U64, 1);
        fb.store(Ty::U64, g, one);
        let slot = fb.alloca(Ty::U64);
        // `alloca` yields a thin `Ptr`; a `PtrToPtr` cast (an address
        // identity the trace follows) gives both arms one type.
        let local = fb.cast(CastOp::PtrToPtr, Ty::Ptr, ptr(), slot);
        let either = fb.select(ptr(), c, pp, local);
        fb.store(Ty::U64, either, one);
        let heap = fb.heap_alloc(Ty::U64, None, None, trust_ir::inst::AllocOrigin::RustHeap);
        fb.dealloc(heap);
        fb.ret(vec![]);
        fb.set_summary(with_effects(effects));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let exact = {
        let mut e = writes(&[p(0), EffectPlace::Global(GlobalId::new(0))]);
        e.allocates = true;
        e.frees = true;
        e
    };
    assert_clean(&build(exact.clone()));
    // Drop the global: refused by name.
    let mut no_global = exact.clone();
    no_global.writes = EffectSet::of([p(0)]);
    let errors = validate_module(&build(no_global));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("mixed".to_string(), "writes")])
    );
    assert!(
        violation_text(&errors, "writes").contains("@COUNTER"),
        "{errors:#?}"
    );
    // Drop the parameter: the Select's parameter arm is still traced.
    let mut no_param = exact.clone();
    no_param.writes = EffectSet::of([EffectPlace::Global(GlobalId::new(0))]);
    let errors = validate_module(&build(no_param));
    assert!(
        violation_text(&errors, "writes").contains("*param0"),
        "{errors:#?}"
    );
    // Drop each flag: each is refused by its own name.
    for flag in ["allocates", "frees"] {
        let mut weaker = exact.clone();
        match flag {
            "allocates" => weaker.allocates = false,
            _ => weaker.frees = false,
        }
        let errors = validate_module(&build(weaker));
        assert_eq!(
            violations(&errors),
            BTreeSet::from([("mixed".to_string(), flag)]),
            "{errors:#?}"
        );
    }
}

/// A loop-carried block parameter is untraceable: a store through it needs
/// `Everything`, even when every incoming value is parameter 0.
#[test]
fn a_block_parameter_is_untraceable() {
    let build = |effects: EffectSummary| {
        let mut mb = ModuleBuilder::new_with_target_info("merge", target());
        let ft = mb.add_func_type(vec![ptr()], vec![]);
        let mut fb = mb.function("merge", ft);
        let entry = fb.create_block();
        let next = fb.create_block();
        let pp = fb.add_block_param(entry, ptr());
        let carried = fb.add_block_param(next, ptr());
        fb.switch_to_block(entry);
        fb.br(next, vec![pp]);
        fb.switch_to_block(next);
        let one = fb.uconst(Ty::U64, 1);
        fb.store(Ty::U64, carried, one);
        fb.ret(vec![]);
        fb.set_summary(with_effects(effects));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let errors = validate_module(&build(writes(&[p(0)])));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("merge".to_string(), "writes")])
    );
    assert_clean(&build(EffectSummary::pure().writing(EffectSet::Everything)));
}

// ---------------------------------------------------------------------------
// the summary's shape
// ---------------------------------------------------------------------------

#[test]
fn a_non_canonical_or_dangling_effect_set_is_refused() {
    for (effects, needle) in [
        (
            EffectSummary::pure().writing(EffectSet::Places(vec![])),
            "not canonical",
        ),
        (
            EffectSummary::pure().writing(EffectSet::Places(vec![p(1), p(0)])),
            "not canonical",
        ),
        (
            EffectSummary::pure().writing(EffectSet::Places(vec![p(0), p(0)])),
            "not canonical",
        ),
        (
            EffectSummary::pure().reading(EffectSet::of([p(5)])),
            "parameter 5",
        ),
        (
            EffectSummary::pure().writing(EffectSet::of([EffectPlace::Global(GlobalId::new(9))])),
            "global #9",
        ),
    ] {
        let mut module = setter(None, EffectSummary::pure());
        module.functions[0].summary = Some(with_effects(effects.clone()));
        let errors = validate_module(&module);
        let details = summary_errors(&errors);
        assert!(
            details.iter().any(|d| d.contains(needle)),
            "{effects:?} must be refused naming {needle:?}: {errors:#?}"
        );
    }
}

// ---------------------------------------------------------------------------
// world epochs
// ---------------------------------------------------------------------------

fn bound(name: &str, sort: ClauseSort, place: ClausePlace) -> (String, ClauseBinding) {
    (name.to_string(), ClauseBinding { sort, place })
}

fn heap() -> ClauseSort {
    ClauseSort::Array(
        Box::new(ClauseSort::BitVec(64)),
        Box::new(ClauseSort::BitVec(64)),
    )
}

/// `(= (select after 0) (select before 0))`, binding `before` and `after`.
fn frame_clause(before: ClausePlace, after: ClausePlace) -> ProofFormula {
    let mut clause = ProofFormula::smtlib2(
        "(= (select after #x0000000000000000) (select before #x0000000000000000))",
        "Bool",
    );
    clause.bindings = vec![
        bound("before", heap(), before),
        bound("after", heap(), after),
    ];
    clause
}

/// A `proved` DECLARATION whose `proved` is backed through an import row
/// (taken on faith by the structural validator), with one ensures clause.
fn declared_contract(ensures: ProofFormula, requires: Option<ProofFormula>) -> Module {
    let mut m = Module::new("epochs");
    m.target_info = Some(target());
    let import = m
        .intern_import(ModuleImport::new(
            "dep",
            trust_ir::proof::ProofDigest::sha256([7u8; 32]),
        ))
        .expect("Module::intern_import: test fixture");
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![ptr()],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut summary = FunctionSummary::new()
        .with_params(vec!["p".to_string()])
        .ensuring(ensures);
    if let Some(requires) = requires {
        summary = summary.requiring(requires);
    }
    let summary = summary
        .proved()
        .backed_by(ExternRef::new(import, "tick").relying_on(ProofId::new(0)));
    let mut f = Function::declaration(FuncId::new(0), "tick", ft, summary);
    f.producer = Some(Producer::TRust);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// Positive: the epoched places relate the world after the call to the world
/// before it on a `proved` contract.
#[test]
fn world_pre_and_post_bind_on_a_proved_ensures() {
    assert_clean(&declared_contract(
        frame_clause(ClausePlace::WorldPre, ClausePlace::WorldPost),
        None,
    ));
}

/// Twin: the legacy un-epoched `World` on the same proved contract is
/// unbindable, refused by name — once per binding that uses it.
#[test]
fn legacy_world_is_unbindable_on_a_proved_summary() {
    let errors = validate_module(&declared_contract(
        frame_clause(ClausePlace::World, ClausePlace::WorldPost),
        None,
    ));
    let details = summary_errors(&errors);
    assert_eq!(details.len(), 1, "{errors:#?}");
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(
        details[0].contains("legacy un-epoched World on a proved summary"),
        "{details:?}"
    );
    // Mutation control: the same clause on an UNPROVED summary is legal —
    // the rule is scoped to `proved`, as WS1.2 ruled.
    let mut unproved = declared_contract(
        frame_clause(ClausePlace::World, ClausePlace::WorldPost),
        None,
    );
    let summary = unproved.functions[0].summary.as_mut().unwrap();
    summary.proved = false;
    summary.backed_by = None;
    assert_clean(&unproved);
}

/// Twin: `WorldPost` (the world at EXIT) on a requires clause is refused;
/// `WorldPre` there is legal.
#[test]
fn world_post_is_illegal_on_a_requires_clause() {
    let mut pre = ProofFormula::smtlib2(
        "(= (select w #x0000000000000000) #x0000000000000000)",
        "Bool",
    );
    pre.bindings = vec![bound("w", heap(), ClausePlace::WorldPre)];
    let ok = frame_clause(ClausePlace::WorldPre, ClausePlace::WorldPost);
    assert_clean(&declared_contract(ok.clone(), Some(pre.clone())));
    pre.bindings = vec![bound("w", heap(), ClausePlace::WorldPost)];
    let errors = validate_module(&declared_contract(ok, Some(pre)));
    let details = summary_errors(&errors);
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(
        details[0].contains("WorldPost, the world at exit, on a requires clause"),
        "{details:?}"
    );
}

// ---------------------------------------------------------------------------
// declarations: admissible only when authenticated (validate_linked_module)
// ---------------------------------------------------------------------------

fn clause() -> ProofFormula {
    ProofFormula::smtlib2("(= 1 1)", "Bool")
}

/// The contract both sides state: `fn f(p: *mut u64) ensures (= 1 1)`, plus
/// `effects`.
fn contract(effects: Option<EffectSummary>) -> FunctionSummary {
    let mut summary = FunctionSummary::new()
        .with_params(vec!["p".to_string()])
        .ensuring(clause());
    summary.effects = effects;
    summary
}

fn certified_postcondition(function: FuncId) -> (ProofObligation, ProofCertificate) {
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (= 1 1)",
    )
    .with_function(function)
    .with_formula(clause());
    let certificate = contract_clean_cic_certificate(&obligation, "contract-prover")
        .expect("(= 1 1) is genuinely kernel-provable");
    (obligation, certificate)
}

/// A dependency defining `fn f(p: *mut u64) { *p = 1 }` with a `proved`
/// contract (kernel-certified) whose effects are `far_effects`.
fn dependency(far_effects: EffectSummary) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("dep", target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![ptr()], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let pp = fb.add_block_param(entry, ptr());
    fb.switch_to_block(entry);
    let one = fb.uconst(Ty::U64, 1);
    fb.store(Ty::U64, pp, one);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let f = module.functions[0].id;
    module.functions[0].summary = Some(contract(Some(far_effects)).proved());
    let (obligation, certificate) = certified_postcondition(f);
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    assert!(
        validate_module(&module).is_empty(),
        "the dependency must validate on its own: {:?}",
        validate_module(&module)
    );
    module
}

/// An importer that declares `f` (backed by the dependency's #0, with
/// `declared` effects) and defines `g(q) { f(q) }` with `writes: *param0`.
fn importer(dep: &Module, declared: Option<EffectSummary>) -> Module {
    let mut m = Module::new("root");
    m.target_info = Some(target());
    let import = m
        .intern_import(
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![ptr()],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let summary = contract(declared)
        .proved()
        .backed_by(ExternRef::new(import, "f").relying_on(ProofId::new(0)));
    let mut f = Function::declaration(FuncId::new(0), "f", ft, summary);
    f.producer = Some(Producer::TRust);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    // g(q: *mut u64) { f(q) }, hand-built against the table above.
    let mut mb = ModuleBuilder::new_with_target_info("scratch", target());
    let gft = mb.add_func_type(vec![ptr()], vec![]);
    assert_eq!(
        gft, ft,
        "the scratch builder allocates the same func-type id"
    );
    let _f = mb.declare_function("f", gft);
    let mut fb = mb.function("g", gft);
    let entry = fb.create_block();
    let q = fb.add_block_param(entry, ptr());
    fb.switch_to_block(entry);
    fb.call_void(FuncId::new(0), vec![q]);
    fb.ret(vec![]);
    fb.set_summary(with_effects(writes(&[p(0)])));
    fb.build();
    let scratch = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut g = scratch.functions[1].clone();
    g.producer = Some(Producer::TRust);
    m.try_add_function(g)
        .expect("Module::try_add_function: test fixture");
    m
}

/// Positive: once `validate_linked_module` authenticates the declaration's
/// `backed_by` (its effects restated exactly), the caller relies on them and
/// keeps its own `writes` tight. The SAME module under the structural
/// validator is refused: the declaration's effects are then just a claim.
#[test]
fn an_authenticated_declaration_summary_is_admissible() {
    let dep = dependency(writes(&[p(0)]));
    let root = importer(&dep, Some(writes(&[p(0)])));
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:#?}", report.errors());

    let errors = validate_module(&root);
    assert_eq!(
        violations(&errors)
            .into_iter()
            .map(|(f, _)| f)
            .collect::<BTreeSet<_>>(),
        BTreeSet::from(["g".to_string()]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
}

/// Twin: the declaration's effects are NOT the far effects (it claims `pure`
/// where the dependency writes `*p`): the citation is refused, and the
/// caller's frame check does not get to use the forged claim.
#[test]
fn a_declaration_that_misstates_the_far_effects_is_refused() {
    let dep = dependency(writes(&[p(0)]));
    let root = importer(&dep, Some(EffectSummary::pure()));
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { site, detail, .. }
                if *site == "backed_by" && detail.contains("local `effects` differ")
        )),
        "{errors:#?}"
    );
    // Control: leaving the declaration's effects UNRECORDED is always sound —
    // the citation re-earns, and the caller havocs (so g must say so).
    let unrecorded = importer(&dep, None);
    let errors =
        validate_linked_module(&unrecorded, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        !errors
            .iter()
            .any(|e| matches!(e, ValidationError::UnauthenticatedImport { .. })),
        "{errors:#?}"
    );
    assert!(
        violations(&errors).contains(&("g".to_string(), "writes")),
        "an unrecorded callee is havoc: {errors:#?}"
    );
}

/// Twin: a far summary that names a module GLOBAL cannot be restated across
/// the edge (a global has no identity there at this version).
#[test]
fn a_restatement_naming_a_global_is_refused() {
    // The dependency's summary names its own global 0 (it declares one).
    let mut dep = dependency(writes(&[p(0)]));
    dep.globals.push(Global {
        name: "G".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let with_global = writes(&[p(0), EffectPlace::Global(GlobalId::new(0))]);
    dep.functions[0].summary.as_mut().unwrap().effects = Some(with_global.clone());
    assert!(
        validate_module(&dep).is_empty(),
        "{:?}",
        validate_module(&dep)
    );
    let mut root = importer(&dep, Some(with_global));
    // The importer must declare a global 0 for the shape rule; it is a
    // DIFFERENT global, which is exactly why the edge refuses the name.
    root.globals.push(dep.globals[0].clone());
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { site, detail, .. }
                if *site == "backed_by" && detail.contains("module global")
        )),
        "{errors:#?}"
    );
}

// ---------------------------------------------------------------------------
// the proof-program rows F-013 closes, ported and named after them
// ---------------------------------------------------------------------------

/// `goal-g1-g8/g6-state-epochs`: a clause must be able to say WHICH world it
/// is about. `WorldPre` and `WorldPost` are distinct places — the validator
/// treats them differently (exit only on ensures) and a clause that swaps them
/// is a different clause — and the un-epoched `World` no longer binds on a
/// proved contract.
#[test]
fn goal_g1_g8_g6_state_epochs() {
    assert_ne!(ClausePlace::WorldPre, ClausePlace::WorldPost);
    assert_ne!(
        frame_clause(ClausePlace::WorldPre, ClausePlace::WorldPost),
        frame_clause(ClausePlace::WorldPost, ClausePlace::WorldPre)
    );
    assert_clean(&declared_contract(
        frame_clause(ClausePlace::WorldPre, ClausePlace::WorldPost),
        None,
    ));
    assert!(
        !validate_module(&declared_contract(
            frame_clause(ClausePlace::World, ClausePlace::World),
            None,
        ))
        .is_empty()
    );
}

/// `goal-g1-g8/g6-effect-summaries`: a typed effect row per summary; the frame
/// is checked (a body that writes beyond its summary is refused); and the
/// obligation content digest — the certificate-cache identity — moves when the
/// effect row changes.
#[test]
fn goal_g1_g8_g6_effect_summaries() {
    let dep = dependency(writes(&[p(0)]));
    let digest = |m: &Module| m.obligation_digest(ProofId::new(0)).expect("scoped digest");
    let mut wider = dep.clone();
    wider.functions[0].summary.as_mut().unwrap().effects =
        Some(EffectSummary::pure().writing(EffectSet::Everything));
    assert_ne!(
        digest(&dep),
        digest(&wider),
        "a changed effect row must change what the contract's obligation means"
    );
    let mut unrecorded = dep.clone();
    unrecorded.functions[0].summary.as_mut().unwrap().effects = None;
    assert_ne!(digest(&dep), digest(&unrecorded));
    // The frame is enforced.
    assert!(!validate_module(&setter(Some(second), writes(&[p(0)]))).is_empty());
    assert_clean(&setter(Some(first), writes(&[p(0)])));
}

/// `producer-clean/io-and-effects`: an effectful Clean definition calling an
/// extern runtime entry point (`l_IO_println`, no summary) is no longer
/// indistinguishable from a pure one — claiming `pure` is refused naming `io`,
/// and only an honest `io` summary validates.
#[test]
fn producer_clean_io_and_effects() {
    let build = |effects: EffectSummary| {
        let mut mb = ModuleBuilder::new_with_target_info("clean_io", target());
        mb.set_default_producer(Producer::Clean);
        let print_ty = mb.add_func_type(vec![ptr()], vec![]);
        let println = mb.declare_function("l_IO_println", print_ty);
        let main_ty = mb.add_func_type(vec![ptr()], vec![]);
        let mut fb = mb.function("main", main_ty);
        let entry = fb.create_block();
        let s = fb.add_block_param(entry, ptr());
        fb.switch_to_block(entry);
        fb.call_void(println, vec![s]);
        fb.ret(vec![]);
        fb.set_summary(with_effects(effects));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let errors = validate_module(&build(EffectSummary::pure()));
    assert!(
        violations(&errors).contains(&("main".to_string(), "io")),
        "{errors:#?}"
    );
    assert!(
        violation_text(&errors, "io").contains("@l_IO_println"),
        "{errors:#?}"
    );
    assert_clean(&build(EffectSummary::top()));
}

// ---------------------------------------------------------------------------
// review (WS1.14 prep, 2026-09-29): adversarial inputs per rule
// ---------------------------------------------------------------------------

/// The address trace names formal parameter `i` only when the entry block's
/// parameters ARE the formals — no edge re-enters the entry block. A back-edge
/// into the entry block makes its parameter a merge of the formal and whatever
/// the edge passes, so a store through it needs `Everything`, even when the
/// edge passes the same parameter back. Control: the same body without the
/// back-edge keeps `writes: [*param0]`.
#[test]
fn an_entry_block_reentered_by_an_edge_does_not_name_the_formals() {
    let build = |reenter: bool, effects: EffectSummary| {
        let mut mb = ModuleBuilder::new_with_target_info("reentry", target());
        let ft = mb.add_func_type(vec![ptr(), Ty::Bool], vec![]);
        let mut fb = mb.function("spin", ft);
        let entry = fb.create_block();
        let exit = fb.create_block();
        let pp = fb.add_block_param(entry, ptr());
        let c = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        let one = fb.uconst(Ty::U64, 1);
        fb.store(Ty::U64, pp, one);
        if reenter {
            fb.condbr(c, entry, vec![pp, c], exit, vec![]);
        } else {
            fb.condbr(c, exit, vec![], exit, vec![]);
        }
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.set_summary(with_effects(effects));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    assert_clean(&build(false, writes(&[p(0)])));
    let errors = validate_module(&build(true, writes(&[p(0)])));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("spin".to_string(), "writes")]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    assert!(
        violation_text(&errors, "writes").contains("Everything"),
        "{errors:#?}"
    );
    assert_clean(&build(
        true,
        EffectSummary::pure().writing(EffectSet::Everything),
    ));
}

/// `ParamPointee` is ONE level deep: a pointer LOADED out of `*param0` is not
/// in `*param0`'s allocation, so a store through it needs `Everything` even
/// though every value involved derives from parameter 0. The load itself is a
/// read of `*param0`.
#[test]
fn a_pointer_loaded_out_of_a_parameter_is_not_that_parameter() {
    let build = |effects: EffectSummary| {
        let mut mb = ModuleBuilder::new_with_target_info("deref2", target());
        let ft = mb.add_func_type(vec![Ty::PtrMut(Box::new(ptr()))], vec![]);
        let mut fb = mb.function("poke", ft);
        let entry = fb.create_block();
        let pp = fb.add_block_param(entry, Ty::PtrMut(Box::new(ptr())));
        fb.switch_to_block(entry);
        let inner = fb.load(ptr(), pp);
        let one = fb.uconst(Ty::U64, 1);
        fb.store(Ty::U64, inner, one);
        fb.ret(vec![]);
        fb.set_summary(with_effects(effects));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let one_level = EffectSummary::pure()
        .reading(EffectSet::of([p(0)]))
        .writing(EffectSet::of([p(0)]));
    let errors = validate_module(&build(one_level));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("poke".to_string(), "writes")]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    // The load is attributed to `*param0`: dropping it from `reads` is refused.
    let errors = validate_module(&build(EffectSummary::pure().writing(EffectSet::Everything)));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("poke".to_string(), "reads")]),
        "{errors:#?}"
    );
    assert_clean(&build(
        EffectSummary::pure()
            .reading(EffectSet::of([p(0)]))
            .writing(EffectSet::Everything),
    ));
}

/// A recursive call relies on the function's OWN summary (the inductive
/// argument over call depth), mapped through the arguments like any call: a
/// self-call that swaps its parameters makes the callee's `*param0` the
/// caller's `*param1`, which a `writes: [*param0]` summary does not cover.
/// Control: the same self-call passing the parameters in order is admitted.
#[test]
fn a_recursive_call_maps_its_own_summary_through_the_arguments() {
    let build = |swap: bool| {
        let mut mb = ModuleBuilder::new_with_target_info("recursion", target());
        let ft = mb.add_func_type(vec![ptr(), ptr(), Ty::Bool], vec![]);
        let mut fb = mb.function("walk", ft);
        let entry = fb.create_block();
        let again = fb.create_block();
        let done = fb.create_block();
        let pp = fb.add_block_param(entry, ptr());
        let qq = fb.add_block_param(entry, ptr());
        let c = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        let one = fb.uconst(Ty::U64, 1);
        fb.store(Ty::U64, pp, one);
        fb.condbr(c, again, vec![], done, vec![]);
        fb.switch_to_block(again);
        let stop = fb.bool_const(false);
        let args = if swap {
            vec![qq, pp, stop]
        } else {
            vec![pp, qq, stop]
        };
        fb.call_void(FuncId::new(0), args);
        fb.br(done, vec![]);
        fb.switch_to_block(done);
        fb.ret(vec![]);
        fb.set_summary(with_effects(writes(&[p(0)])));
        let id = fb.build();
        assert_eq!(id, FuncId::new(0), "the self-call names this function");
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    assert_clean(&build(false));
    let errors = validate_module(&build(true));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("walk".to_string(), "writes")]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    assert!(
        violation_text(&errors, "writes").contains("*param1"),
        "{errors:#?}"
    );
}

/// `Invoke` and `Resume` each force `may_unwind`: the exact summary validates,
/// and without the flag both are refused by name.
#[test]
fn invoke_and_resume_need_may_unwind() {
    let build = |effects: EffectSummary| {
        let mut mb = ModuleBuilder::new_with_target_info("unwinds", target());
        let callee_ty = mb.add_func_type(vec![ptr()], vec![]);
        let mut fb = mb.function("callee", callee_ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, ptr());
        fb.switch_to_block(entry);
        let v = fb.uconst(Ty::U64, 3);
        fb.store(Ty::U64, a, v);
        fb.ret(vec![]);
        fb.set_summary(with_effects(writes(&[p(0)])));
        let callee = fb.build();
        let caller_ty = mb.add_func_type(vec![ptr()], vec![]);
        let mut fb = mb.function("caller", caller_ty);
        let entry = fb.create_block();
        let ok = fb.create_block();
        let pad = fb.create_block();
        let pp = fb.add_block_param(entry, ptr());
        fb.switch_to_block(entry);
        fb.invoke_void(callee, vec![pp], ok, vec![], pad);
        fb.switch_to_block(ok);
        fb.ret(vec![]);
        fb.switch_to_block(pad);
        let (exn, _selector) = fb.landingpad(true, vec![]);
        fb.resume(exn);
        fb.set_summary(with_effects(effects));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let mut exact = writes(&[p(0)]);
    exact.may_unwind = true;
    assert_clean(&build(exact));
    let errors = validate_module(&build(writes(&[p(0)])));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([("caller".to_string(), "may_unwind")]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
}

/// An admissible callee's FLAGS are the caller's too: a call to a defined
/// callee whose summary says it may unwind and performs I/O needs both flags,
/// each refused by its own name, and the honest caller summary validates.
#[test]
fn a_callee_passes_its_flags_on() {
    let mut flagged = writes(&[p(0)]);
    flagged.may_unwind = true;
    flagged.io = true;
    let callee = Some(with_effects(flagged));
    let errors = validate_module(&caller_module(
        callee.clone(),
        false,
        false,
        writes(&[p(0)]),
    ));
    assert_eq!(
        violations(&errors),
        BTreeSet::from([
            ("caller".to_string(), "may_unwind"),
            ("caller".to_string(), "io")
        ]),
        "{errors:#?}"
    );
    assert!(only_effect_violations(&errors), "{errors:#?}");
    let mut honest = writes(&[p(0)]);
    honest.may_unwind = true;
    honest.io = true;
    assert_clean(&caller_module(callee, false, false, honest));
}

/// The declaration rule's premise: a far DEFINITION's effects are checked
/// against its body in the dependency's own pass. A dependency that claims
/// `pure` for a body writing `*p` is itself invalid, so no importer can
/// authenticate a restatement of that claim — even an exact one.
#[test]
fn a_dependency_whose_body_breaks_its_effects_backs_nothing() {
    let mut dep = dependency(writes(&[p(0)]));
    dep.functions[0].summary.as_mut().unwrap().effects = Some(EffectSummary::pure());
    let dep_errors = validate_module(&dep);
    assert_eq!(
        violations(&dep_errors),
        BTreeSet::from([("f".to_string(), "writes")]),
        "the lying dependency is refused on its own: {dep_errors:#?}"
    );
    assert!(
        only_effect_violations(&dep_errors),
        "and ONLY for its effects (the twin isolates the rule): {dep_errors:#?}"
    );
    let root = importer(&dep, Some(EffectSummary::pure()));
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { first, .. }
                if first.contains("effect summary")
        )),
        "{errors:#?}"
    );
}

/// `WorldPost` (the world at exit) on a `decreases` measure is refused like on
/// a `requires` clause: a termination measure is evaluated on entry. Control:
/// `WorldPre` there is legal.
#[test]
fn world_post_is_illegal_on_a_decreases_measure() {
    let measure = |place: ClausePlace| {
        let mut m = ProofFormula::smtlib2("(select w #x0000000000000000)", "(_ BitVec 64)");
        m.bindings = vec![bound("w", heap(), place)];
        m
    };
    let with_measure = |place: ClausePlace| {
        let mut module = declared_contract(
            frame_clause(ClausePlace::WorldPre, ClausePlace::WorldPost),
            None,
        );
        module.functions[0]
            .summary
            .as_mut()
            .unwrap()
            .decreases
            .push(measure(place));
        module
    };
    assert_clean(&with_measure(ClausePlace::WorldPre));
    let errors = validate_module(&with_measure(ClausePlace::WorldPost));
    let details = summary_errors(&errors);
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(
        details[0].contains("WorldPost, the world at exit, on a decreases clause"),
        "{details:?}"
    );
}

// ---------------------------------------------------------------------------
// rebase onto main (2026-10-07): the instructions main gained while this line
// was in review — the sited check and `AssertInvoke` (amendment P), the
// call-unwind boundaries, `DropInvoke` and `InvokeIndirect` (amendment D).
// Each is classified by the effect trace; each has a positive and a twin.
// ---------------------------------------------------------------------------

mod rebase_instructions {
    use super::*;
    use trust_ir::value::{BlockId, FuncTyId, ValueId};
    use trust_ir::{
        AssertKind, Block, CallingConv, ICmpOp, Inst, InstrNode, PanicLocation, PanicSite,
    };

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }
    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    fn loc_global() -> Global {
        Global {
            name: "loc".to_string(),
            ty: Ty::U64,
            mutable: false,
            initializer: Some(Constant::Int(7)),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        }
    }

    /// How the panic entry is spelled.
    #[derive(Clone, Copy, PartialEq)]
    enum EntryKind {
        /// A definition that reads its location (`*param2`) and traps, with
        /// that exact summary.
        ReadsLocation,
        /// A body-less declaration: no admissible summary (havoc).
        Declaration,
    }

    /// How the check reaches its failure path.
    #[derive(Clone, Copy, PartialEq)]
    enum Check {
        /// No site: a failed check traps.
        Unsited,
        /// `assert` sited on `@loc` (a static location).
        SitedStatic,
        /// `assert` sited on the check's own pointer parameter `%p`.
        SitedParam,
        /// `assert_invoke` sited on `@loc`, unwinding into a pad that traps.
        Invoke,
    }

    /// `panic_entry(i: usize, n: usize, loc: ptr)` (function 0) and
    /// `check(i: usize, n: usize, p: ptr) -> usize` (function 1), which checks
    /// `i < n` as `check` says and carries `effects`.
    fn sited(entry_kind: EntryKind, check: Check, effects: EffectSummary) -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("sited_check_effects", target());
        let entry_ty = mb.add_func_type(vec![Ty::Usize, Ty::Usize, Ty::Ptr], vec![]);
        let entry = match entry_kind {
            EntryKind::Declaration => mb.declare_function("panic_entry", entry_ty),
            EntryKind::ReadsLocation => {
                let mut fb = mb.function("panic_entry", entry_ty);
                let bb = fb.create_block();
                let _i = fb.add_block_param(bb, Ty::Usize);
                let _n = fb.add_block_param(bb, Ty::Usize);
                let loc = fb.add_block_param(bb, Ty::Ptr);
                fb.switch_to_block(bb);
                let _ = fb.load(Ty::U64, loc);
                fb.unreachable();
                fb.set_summary(with_effects(
                    EffectSummary::pure().reading(EffectSet::of([p(2)])),
                ));
                fb.build()
            }
        };
        mb.add_global(loc_global());
        let ft = mb.add_func_type(vec![Ty::Usize, Ty::Usize, Ty::Ptr], vec![Ty::Usize]);
        let mut fb = mb.function("check", ft);
        let bb = fb.create_block();
        let i = fb.add_block_param(bb, Ty::Usize);
        let n = fb.add_block_param(bb, Ty::Usize);
        let pp = fb.add_block_param(bb, Ty::Ptr);
        fb.switch_to_block(bb);
        let in_range = fb.icmp(ICmpOp::Ult, Ty::Usize, i, n);
        let kind = AssertKind::BoundsCheck { index: i, len: n };
        let at_loc = PanicSite {
            entry,
            location: PanicLocation::Global(GlobalId::new(0)),
        };
        match check {
            Check::Unsited => fb.assert(in_range),
            Check::SitedStatic => fb.assert_sited(in_range, kind, at_loc),
            Check::SitedParam => fb.assert_sited(
                in_range,
                kind,
                PanicSite {
                    entry,
                    location: PanicLocation::Value(pp),
                },
            ),
            Check::Invoke => {
                let normal = fb.create_block();
                let pad = fb.create_block();
                fb.assert_invoke(in_range, kind, at_loc, normal, vec![], pad);
                fb.switch_to_block(pad);
                let _ = fb.landingpad(true, vec![]);
                fb.unreachable();
                fb.switch_to_block(normal);
            }
        }
        fb.ret(vec![i]);
        fb.set_summary(with_effects(effects));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    fn reads_loc() -> EffectSummary {
        EffectSummary::pure().reading(EffectSet::of([EffectPlace::Global(GlobalId::new(0))]))
    }

    /// Control: an UNSITED check traps and calls nothing, so the pure summary
    /// holds even with a havoc entry in the module.
    #[test]
    fn an_unsited_check_touches_nothing() {
        assert_clean(&sited(
            EntryKind::Declaration,
            Check::Unsited,
            EffectSummary::pure(),
        ));
    }

    /// A sited check's failure calls its entry with the location: an entry
    /// that reads its location makes the check read `@loc`.
    #[test]
    fn a_sited_check_reads_what_its_entry_reads_through_the_location() {
        assert_clean(&sited(
            EntryKind::ReadsLocation,
            Check::SitedStatic,
            reads_loc(),
        ));
        let errors = validate_module(&sited(
            EntryKind::ReadsLocation,
            Check::SitedStatic,
            EffectSummary::pure(),
        ));
        assert_eq!(
            violations(&errors),
            BTreeSet::from([("check".to_string(), "reads")]),
            "{errors:#?}"
        );
        assert!(only_effect_violations(&errors), "{errors:#?}");
        assert!(
            violation_text(&errors, "reads").contains("@loc"),
            "the refusal names the location global: {errors:#?}"
        );
    }

    /// A run-time location is the check's own parameter: the entry's
    /// `*param2` maps to the check's `*param2`, not to `@loc`.
    #[test]
    fn a_run_time_location_maps_through_the_argument() {
        assert_clean(&sited(
            EntryKind::ReadsLocation,
            Check::SitedParam,
            EffectSummary::pure().reading(EffectSet::of([p(2)])),
        ));
        let errors = validate_module(&sited(
            EntryKind::ReadsLocation,
            Check::SitedParam,
            reads_loc(),
        ));
        assert_eq!(
            violations(&errors),
            BTreeSet::from([("check".to_string(), "reads")]),
            "{errors:#?}"
        );
        assert!(
            violation_text(&errors, "reads").contains("*param2"),
            "{errors:#?}"
        );
    }

    /// A sited check whose entry has no admissible summary (a body-less
    /// declaration, unauthenticated) is havoc: every side and every flag.
    #[test]
    fn a_sited_check_on_a_havoc_entry_is_the_top_summary() {
        assert_clean(&sited(
            EntryKind::Declaration,
            Check::SitedStatic,
            EffectSummary::top(),
        ));
        let errors = validate_module(&sited(
            EntryKind::Declaration,
            Check::SitedStatic,
            reads_loc(),
        ));
        let check = |effect| ("check".to_string(), effect);
        assert_eq!(
            violations(&errors),
            BTreeSet::from([
                check("reads"),
                check("writes"),
                check("allocates"),
                check("frees"),
                check("may_unwind"),
                check("io"),
            ]),
            "{errors:#?}"
        );
        assert!(only_effect_violations(&errors), "{errors:#?}");
    }

    /// `AssertInvoke` may enter its pad, so it needs `may_unwind` even when the
    /// pad traps (no `Resume` to flag it) and its entry cannot unwind.
    #[test]
    fn assert_invoke_needs_may_unwind() {
        let mut unwinding = reads_loc();
        unwinding.may_unwind = true;
        assert_clean(&sited(EntryKind::ReadsLocation, Check::Invoke, unwinding));
        let errors = validate_module(&sited(EntryKind::ReadsLocation, Check::Invoke, reads_loc()));
        assert_eq!(
            violations(&errors),
            BTreeSet::from([("check".to_string(), "may_unwind")]),
            "{errors:#?}"
        );
        assert!(only_effect_violations(&errors), "{errors:#?}");
    }

    /// The entry-block re-entry rule reads main's successor table: an
    /// `AssertInvoke` whose NORMAL edge re-enters the entry block makes the
    /// entry parameters untraceable (they are no longer the formals).
    #[test]
    fn an_assert_invoke_back_edge_to_the_entry_block_makes_params_untraceable() {
        let mut m = sited(
            EntryKind::ReadsLocation,
            Check::SitedParam,
            EffectSummary::pure().reading(EffectSet::of([p(2)])),
        );
        assert_clean(&m);
        // Rewrite `check` so `bb0` ends in an assert_invoke whose normal edge
        // loops back to bb0 with the same arguments.
        let check = m.functions.iter_mut().find(|f| f.name == "check").unwrap();
        let entry = check.entry;
        let (cond, i, n, pp) = match (&check.blocks[0].body[0], &check.blocks[0].params[..]) {
            (node, [(i, _), (n, _), (pp, _)]) if matches!(node.inst, Inst::ICmp { .. }) => {
                (node.results[0], *i, *n, *pp)
            }
            other => panic!("unexpected shape {other:?}"),
        };
        let body = &mut check.blocks[0].body;
        let entry_fn = FuncId::new(0);
        let site = PanicSite {
            entry: entry_fn,
            location: PanicLocation::Value(pp),
        };
        body.truncate(1);
        body.push(InstrNode::new(Inst::AssertInvoke {
            cond,
            kind: AssertKind::BoundsCheck { index: i, len: n },
            site,
            normal_dest: entry,
            normal_args: vec![i, n, pp],
            unwind_dest: b(1),
        }));
        let mut pad = Block::new(b(1));
        pad.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .with_results(vec![v(90), v(91)]),
        );
        pad.body.push(InstrNode::new(Inst::Unreachable));
        check.blocks.push(pad);
        let mut summary = EffectSummary::pure().reading(EffectSet::of([p(2)]));
        summary.may_unwind = true;
        check.summary = Some(with_effects(summary));
        let errors = validate_module(&m);
        assert!(
            violations(&errors).contains(&("check".to_string(), "reads")),
            "a re-entered entry block's parameter is not the formal: {errors:#?}"
        );
        assert!(
            violation_text(&errors, "reads").contains("does not trace"),
            "{errors:#?}"
        );
    }

    /// `fn set(p, q) { *p = 7 }` with `writes: [*param0]` (function 0) and a
    /// caller `fn f(a, b)` (function 1) that calls `set(b, a)` through `inst`.
    fn boundary_caller(make: fn(FuncId, Vec<ValueId>) -> Inst, effects: EffectSummary) -> Module {
        let mut m = setter(Some(first), writes(&[p(0)]));
        // `set`'s own signature, `(ptr, ptr) -> ()`.
        let sig = FuncTyId::new(0);
        let mut f = Function::new(FuncId::new(1), "f", sig, b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), ptr()));
        entry.params.push((v(1), ptr()));
        entry
            .body
            .push(InstrNode::new(make(FuncId::new(0), vec![v(1), v(0)])));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(entry);
        f.summary = Some(with_effects(effects));
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        m
    }

    fn plain(callee: FuncId, args: Vec<ValueId>) -> Inst {
        Inst::Call { callee, args }
    }

    fn cannot_unwind(callee: FuncId, args: Vec<ValueId>) -> Inst {
        Inst::CallCannotUnwind { callee, args }
    }

    /// `CallCannotUnwind` is a direct call: the callee's admissible summary
    /// maps through the arguments exactly as for `Call` (swapped here).
    #[test]
    fn a_cannot_unwind_call_maps_the_callee_summary_like_a_call() {
        for make in [plain as fn(_, _) -> Inst, cannot_unwind] {
            assert_clean(&boundary_caller(make, writes(&[p(1)])));
            let errors = validate_module(&boundary_caller(make, writes(&[p(0)])));
            assert_eq!(
                violations(&errors),
                BTreeSet::from([("f".to_string(), "writes")]),
                "{errors:#?}"
            );
            assert!(only_effect_violations(&errors), "{errors:#?}");
            assert!(
                violation_text(&errors, "writes").contains("*param1"),
                "{errors:#?}"
            );
        }
    }

    /// The boundary does not hide the callee's flags: a callee that may unwind
    /// still makes the caller's `may_unwind` necessary (an over-approximation,
    /// never a claim that the boundary is enforced).
    #[test]
    fn a_cannot_unwind_call_still_propagates_the_callee_flags() {
        let mut m = boundary_caller(cannot_unwind, writes(&[p(1)]));
        let set = m.functions.iter_mut().find(|f| f.name == "set").unwrap();
        let mut unwinding = writes(&[p(0)]);
        unwinding.may_unwind = true;
        set.summary = Some(with_effects(unwinding));
        let errors = validate_module(&m);
        assert_eq!(
            violations(&errors),
            BTreeSet::from([("f".to_string(), "may_unwind")]),
            "{errors:#?}"
        );
    }

    /// Every instruction whose callee is unknowable here — an indirect call
    /// (with or without the unwind boundary), `InvokeIndirect`, and
    /// `DropInvoke` (a destructor) — is the top summary.
    #[test]
    fn indirect_and_destructor_twins_are_the_top_summary() {
        fn module(inst: fn() -> Inst, effects: EffectSummary) -> Module {
            let mut m = Module::new("top_twins");
            m.target_info = Some(target());
            let sig = m
                .add_func_type(FuncTy {
                    abi: None,
                    params: vec![Ty::Ptr],
                    returns: vec![],
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            // func.0 `id(%0: ptr) {}` — a valid indirect callee.
            let mut id = Function::new(FuncId::new(0), "id", sig, b(0));
            let mut block = Block::new(b(0));
            block.params.push((v(0), Ty::Ptr));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            id.blocks.push(block);
            m.try_add_function(id)
                .expect("Module::try_add_function: test fixture");
            // func.1 `f(%0: ptr)`: bb0 computes `%1 = fn @id` then `inst`;
            // bb1 returns; bb2 is a cleanup pad that traps.
            let mut f = Function::new(FuncId::new(1), "f", sig, b(0));
            let mut entry = Block::new(b(0));
            entry.params.push((v(0), Ty::Ptr));
            entry.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Func(sig),
                    value: Constant::FnDef(FuncId::new(0)),
                })
                .with_results(vec![v(1)]),
            );
            let inst = inst();
            let terminates = !inst.successor_edges().is_empty();
            entry.body.push(InstrNode::new(inst));
            if !terminates {
                entry
                    .body
                    .push(InstrNode::new(Inst::Return { values: vec![] }));
            }
            f.blocks.push(entry);
            if terminates {
                let mut normal = Block::new(b(1));
                normal
                    .body
                    .push(InstrNode::new(Inst::Return { values: vec![] }));
                f.blocks.push(normal);
                let mut pad = Block::new(b(2));
                pad.body.push(
                    InstrNode::new(Inst::LandingPad {
                        is_cleanup: true,
                        catch_type_indices: vec![],
                    })
                    .with_results(vec![v(2), v(3)]),
                );
                pad.body.push(InstrNode::new(Inst::Unreachable));
                f.blocks.push(pad);
            }
            f.summary = Some(with_effects(effects));
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            m
        }
        type Twin = (&'static str, fn() -> Inst);
        let twins: [Twin; 3] = [
            ("call_indirect_cannot_unwind", || {
                Inst::CallIndirectCannotUnwind {
                    callee: v(1),
                    sig: FuncTyId::new(0),
                    args: vec![v(0)],
                    calling_conv: CallingConv::C,
                }
            }),
            ("invoke_indirect", || Inst::InvokeIndirect {
                callee: v(1),
                sig: FuncTyId::new(0),
                args: vec![v(0)],
                calling_conv: CallingConv::C,
                normal_dest: b(1),
                normal_args: vec![],
                unwind_dest: b(2),
            }),
            ("drop_invoke", || Inst::DropInvoke {
                ty: Ty::Struct(trust_ir::value::StructId::new(0)),
                ptr: v(0),
                normal_dest: b(1),
                normal_args: vec![],
                unwind_dest: b(2),
            }),
        ];
        for (name, inst) in twins {
            let mut top = module(inst, EffectSummary::top());
            let mut pure = module(inst, EffectSummary::pure());
            if name == "drop_invoke" {
                for m in [&mut top, &mut pure] {
                    m.add_struct(trust_ir::ty::StructDef {
                        id: trust_ir::value::StructId::new(0),
                        name: "S0".into(),
                        fields: vec![trust_ir::ty::FieldDef {
                            name: "data".into(),
                            ty: Ty::Ptr,
                            offset: Some(0),
                        }],
                        size: Some(8),
                        align: Some(8),
                        repr: Default::default(),
                        origin: None,
                    });
                    m.set_drop_glue(
                        Ty::Struct(trust_ir::value::StructId::new(0)),
                        FuncId::new(0),
                    )
                    .unwrap();
                }
            }
            let errors = validate_module(&top);
            assert!(
                errors.is_empty(),
                "{name}: the top summary admits it: {errors:#?}"
            );
            let errors = validate_module(&pure);
            let f = |effect| ("f".to_string(), effect);
            assert_eq!(
                violations(&errors),
                BTreeSet::from([
                    f("reads"),
                    f("writes"),
                    f("allocates"),
                    f("frees"),
                    f("may_unwind"),
                    f("io"),
                ]),
                "{name}: {errors:#?}"
            );
            assert!(only_effect_violations(&errors), "{name}: {errors:#?}");
        }
    }

    /// WS4.4 (landed meanwhile) resolves a MODULE obligation's bindings
    /// against its owning function. The world epochs are epochs of that
    /// function's call: an unscoped obligation may not bind them, `WorldPost`
    /// (the world at exit) takes the post-state rule `MutParamExit` takes, and
    /// `WorldPre` is legal on every kind.
    #[test]
    fn a_module_obligation_binds_the_world_epochs_by_the_post_state_rule() {
        fn module(kind: ObligationKind, place: ClausePlace, scoped: bool) -> Module {
            let mut m = setter(Some(first), writes(&[p(0)]));
            let mut formula = ProofFormula::smtlib2("(= h h)", "Bool");
            formula.bindings = vec![(
                "h".to_string(),
                ClauseBinding {
                    sort: ClauseSort::Array(
                        Box::new(ClauseSort::BitVec(64)),
                        Box::new(ClauseSort::BitVec(64)),
                    ),
                    place,
                },
            )];
            let mut o = ProofObligation::new(ProofId::new(0), kind, ProofStatus::Pending, "o")
                .with_formula(formula);
            if scoped {
                o = o.with_function(FuncId::new(0));
            }
            m.proof_obligations.push(o);
            m
        }
        fn refusals(m: &Module) -> Vec<String> {
            validate_module(m)
                .into_iter()
                .filter_map(|e| match e {
                    ValidationError::InvalidObligationBinding { detail, .. } => Some(detail),
                    _ => None,
                })
                .collect()
        }
        // Accepted: entry epoch on any kind; exit epoch on the post-state kinds.
        for (kind, place) in [
            (ObligationKind::Precondition, ClausePlace::WorldPre),
            (ObligationKind::PanicFreedom, ClausePlace::WorldPre),
            (ObligationKind::Postcondition, ClausePlace::WorldPre),
            (ObligationKind::Postcondition, ClausePlace::WorldPost),
            (ObligationKind::GiveBackRefinement, ClausePlace::WorldPost),
        ] {
            let m = module(kind.clone(), place, true);
            assert_eq!(refusals(&m), Vec::<String>::new(), "{kind:?} {place:?}");
        }
        // Refused: the exit epoch before the call has returned.
        for kind in [
            ObligationKind::Precondition,
            ObligationKind::PanicFreedom,
            ObligationKind::LoopInvariant,
        ] {
            let refused = refusals(&module(kind.clone(), ClausePlace::WorldPost, true));
            assert!(
                refused.len() == 1 && refused[0].contains("world at exit"),
                "{kind:?}: {refused:?}"
            );
        }
        // Refused: either epoch with no function to be an epoch of.
        for place in [ClausePlace::WorldPre, ClausePlace::WorldPost] {
            let refused = refusals(&module(ObligationKind::Postcondition, place, false));
            assert!(
                refused.len() == 1 && refused[0].contains("may bind only World"),
                "{place:?}: {refused:?}"
            );
        }
    }
}
