// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Independent strict/DAG replay of the raw64 word and a bounded authored Core
//! consumer. No extracted frontend, TLA, native, no-overflow or default-package
//! authority follows. Actual checked canonical arithmetic is explicitly owned.

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker, TypeError};
use std::sync::OnceLock;
use trust_ir::{BlockId, Endianness, FuncId, OverflowOp, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::{
    ModuleBuilder,
    core_execution::{
        Assembler, Catalog, Coordinate, Current, EntryTarget, ExactRun, Limits, MachineModel,
        NatTerm, OverflowPremises, PendingEquality, PendingProof, ValueBindingPremises,
    },
    core_reflection::reflect_core_module_v1,
    scoped_local::{LocalScope, ScopedLocal},
};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn limit() -> Expr {
    app("ir_nat_pow2", [nat(64)])
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn raw(a: Expr, b: Expr) -> Expr {
    app("ir_wrap", [nat(64), app("Nat.add", [a, b])])
}
fn bound(word: Expr) -> Expr {
    app("Nat.lt", [word, limit()])
}
fn fast(a: Expr, b: Expr) -> Expr {
    let sum = app("Nat.add", [a, b]);
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, c("Bool"), c("Nat")),
            app("Nat.sub", [sum.clone(), limit()]),
            sum.clone(),
            app("ir_nat_ltb", [sum, limit()]),
        ],
    )
}
fn bounded(value: u64) -> PendingProof {
    PendingProof::candidate(
        bound(nat(value)),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(value)]), nat(u64::MAX - value)],
        ),
    )
}
fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn environment() -> &'static Environment {
    static ENVIRONMENT: OnceLock<Environment> = OnceLock::new();
    ENVIRONMENT.get_or_init(|| {
        clean_verify::eval_ir::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
            .expect("actual public checked canonical-arithmetic owner")
            .into_environment()
    })
}
fn closed(
    scope: &LocalScope,
    parameters: &[ScopedLocal],
    term: &Expr,
    proposition: &Expr,
) -> (Expr, Expr) {
    let term = parameters
        .iter()
        .rev()
        .fold(term.clone(), |body, local| local.lam(body));
    let proposition = parameters
        .iter()
        .rev()
        .fold(proposition.clone(), |body, local| local.pi(body));
    (
        scope.close(&term).unwrap(),
        scope.close(&proposition).unwrap(),
    )
}
fn check(term: &Expr, proposition: &Expr, accepted: bool, roots: &[&str]) {
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    assert!(!proposition.has_fvar_quick() && !proposition.has_loose_bvars());
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    assert_eq!(checker.heartbeat_limit(), 2_000_000);
    checker
        .check_type(proposition, &Expr::sort(Level::zero()))
        .unwrap();
    let result = checker.check_type(term, proposition);
    assert!(
        !checker.heartbeat_spent(),
        "resource stop is not a verdict: {result:?}"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    if accepted {
        result.unwrap();
        let audit = environment().audit_certification(proposition, term);
        assert!(audit.is_certified(), "actual rooted closure: {audit:#?}");
        for root in roots {
            let root = Name::from_string(root);
            assert!(audit.dependencies.contains(&root));
            assert!(environment().axiom_deps(&root).unwrap().is_empty());
            assert!(
                environment()
                    .foundational_axiom_deps(&root)
                    .unwrap()
                    .is_empty()
            );
            assert!(environment().trust_marker_deps(&root).unwrap().is_empty());
        }
    } else {
        assert!(
            matches!(result, Err(TypeError::TypeMismatch { .. })),
            "{result:?}"
        );
    }
}
fn replay(
    scope: &LocalScope,
    parameters: &[ScopedLocal],
    term: &Expr,
    proposition: &Expr,
    roots: &[&str],
) {
    let (term, proposition) = closed(scope, parameters, term, proposition);
    check(&term, &proposition, true, roots);
    let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
    assert_eq!(decoded, term);
    check(&decoded, &proposition, true, roots);
}
fn refuse(scope: &LocalScope, parameters: &[ScopedLocal], term: &Expr, proposition: &Expr) {
    let (term, proposition) = closed(scope, parameters, term, proposition);
    check(&term, &proposition, false, &[]);
}

#[test]
fn universal_wrapped_add_derives_original_raw_equality_and_bound_from_inputs_only() {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let a = assembler.local(c("Nat")).unwrap();
    let b = assembler.local(c("Nat")).unwrap();
    let ha = assembler.local(bound(a.term().clone())).unwrap();
    let hb = assembler.local(bound(b.term().clone())).unwrap();
    let before = assembler.operations();
    let (word, equality, output) = assembler
        .byte_add_word64_canonical(
            a.term().clone(),
            b.term().clone(),
            PendingProof::candidate(bound(a.term().clone()), ha.term().clone()),
            PendingProof::candidate(bound(b.term().clone()), hb.term().clone()),
        )
        .unwrap();
    let expected = raw(a.term().clone(), b.term().clone());
    assert_eq!(word, expected);
    assert_eq!(assembler.operations(), before + 1);
    assert_eq!(assembler.local_scope().allocated(), 4);
    let equality_goal = eq(
        c("Nat"),
        expected.clone(),
        fast(a.term().clone(), b.term().clone()),
    );
    let bound_goal = bound(expected);
    let parameters = [a, b, ha, hb];
    replay(
        &scope,
        &parameters,
        equality.term(),
        &equality_goal,
        &["ir_byte_add_wrap_bounded_sum_v1"],
    );
    replay(
        &scope,
        &parameters,
        output.term(),
        &bound_goal,
        &[
            "ir_byte_add_wrap_bounded_sum_v1",
            "ir_byte_add_word_bound_v1",
        ],
    );
}

#[test]
fn inhabited_wrapped_add_crossings_match_independent_literals_without_raw_modulus_reduction() {
    for (a, b) in [
        (0, 0),
        (14, 3),
        (i64::MAX as u64, 1),
        (u64::MAX, 1),
        (u64::MAX, u64::MAX),
    ] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let (_, equality, output) = assembler
            .byte_add_word64_canonical(nat(a), nat(b), bounded(a), bounded(b))
            .unwrap();
        let expected_raw = raw(nat(a), nat(b));
        replay(
            assembler.local_scope(),
            &[],
            equality.term(),
            &eq(c("Nat"), expected_raw.clone(), fast(nat(a), nat(b))),
            &["ir_byte_add_wrap_bounded_sum_v1"],
        );
        replay(
            assembler.local_scope(),
            &[],
            output.term(),
            &bound(expected_raw.clone()),
            &["ir_byte_add_word_bound_v1"],
        );
        // Normalize only the bounded conditional result, not raw full64 modulo.
        let literal = nat(a.wrapping_add(b));
        let fast_to_literal = assembler
            .conversion(c("Nat"), equality.right().clone(), literal.clone())
            .unwrap();
        let exact = assembler.compose(equality, fast_to_literal).unwrap();
        replay(
            assembler.local_scope(),
            &[],
            exact.term(),
            &eq(c("Nat"), expected_raw, literal),
            &["ir_byte_add_wrap_bounded_sum_v1"],
        );
    }
}

#[test]
fn wrapped_add_false_bounds_wrong_width_order_operands_and_forged_evidence_are_semantic_refusals() {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let (_, equality, output) = assembler
        .byte_add_word64_canonical(nat(14), nat(3), bounded(14), bounded(3))
        .unwrap();
    let sum = app("Nat.add", [nat(14), nat(3)]);
    let reversed = Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, c("Bool"), c("Nat")),
            sum.clone(),
            app("Nat.sub", [sum.clone(), limit()]),
            app("ir_nat_ltb", [sum, limit()]),
        ],
    );
    for left in [
        raw(nat(13), nat(3)),
        raw(nat(14), nat(4)),
        app("ir_wrap", [nat(4), app("Nat.add", [nat(14), nat(3)])]),
    ] {
        refuse(
            assembler.local_scope(),
            &[],
            equality.term(),
            &eq(c("Nat"), left, fast(nat(14), nat(3))),
        );
    }
    refuse(
        assembler.local_scope(),
        &[],
        equality.term(),
        &eq(c("Nat"), raw(nat(14), nat(3)), reversed),
    );
    refuse(
        assembler.local_scope(),
        &[],
        output.term(),
        &app("Nat.lt", [raw(nat(14), nat(3)), nat(17)]),
    );
    for right_side in [false, true] {
        let forged = PendingProof::candidate(
            bound(nat(if right_side { 3 } else { 14 })),
            app("Nat.le_refl", [nat(if right_side { 3 } else { 14 })]),
        );
        let (ha, hb) = if right_side {
            (bounded(14), forged)
        } else {
            (forged, bounded(3))
        };
        let (_, equality, output) = assembler
            .byte_add_word64_canonical(nat(14), nat(3), ha, hb)
            .unwrap();
        refuse(
            assembler.local_scope(),
            &[],
            equality.term(),
            &eq(c("Nat"), raw(nat(14), nat(3)), fast(nat(14), nat(3))),
        );
        refuse(
            assembler.local_scope(),
            &[],
            output.term(),
            &bound(raw(nat(14), nat(3))),
        );
    }
}

fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, value| {
            app("IRList.cons", [c(ty), value.clone(), tail])
        })
}
fn scalar(word: Expr) -> Expr {
    app("IRScalar.int_", [word])
}
fn boolean(value: bool) -> Expr {
    app(
        "IRScalar.bool_",
        [c(if value { "Bool.true" } else { "Bool.false" })],
    )
}
fn providers() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        c("Nat"),
        Expr::lam(
            BinderInfo::Default,
            app("IRList", [c("IRScalar")]),
            Expr::lam(
                BinderInfo::Default,
                c("IRByteMemoryV1"),
                Expr::lam(
                    BinderInfo::Default,
                    c("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            c("Nat"),
                            app("IROutcome.stuck", [c("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
}
fn memory() -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(16), nat(16), nat(0), c("Bool.true")],
                    ),
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(80), nat(8), nat(7), c("Bool.false")],
                    ),
                ],
            ),
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                app("IROption.some", [c("Nat"), nat(173)]),
            ),
            nat(128),
        ],
    )
}
fn truth(assembler: &mut Assembler<'_>, proposition: Expr) -> PendingEquality {
    assembler
        .conversion(c("Bool"), proposition, c("Bool.true"))
        .unwrap()
}

#[test]
fn fetched_wrapped_add_keeps_both_overflow_lanes_actual_binding_fuel_and_complete_world() {
    for (signed, a, b) in [
        (false, 14, 3),
        (false, u64::MAX, 1),
        (true, i64::MAX as u64, 1),
    ] {
        let ty = if signed { Ty::I64 } else { Ty::U64 };
        let mut builder = ModuleBuilder::new_with_target_info(
            "authored_raw_wrapped_add",
            TargetInfo {
                triple: "aarch64-apple-darwin".into(),
                pointer_size: 8,
                endianness: Endianness::Little,
                abi: Some("aapcs64".into()),
                struct_passing: StructPassingPolicy::NativeC,
            },
        );
        let signature =
            builder.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone(), Ty::Bool]);
        let fid = builder.declare_function("wrapped_add", signature);
        let mut function = builder.define_function(fid).unwrap();
        let bid = function.create_block();
        let left = function.add_block_param(bid, ty.clone());
        let right = function.add_block_param(bid, ty);
        function.switch_to_block(bid);
        let (value, flag) = function.overflow(
            OverflowOp::AddOverflow,
            if signed { Ty::I64 } else { Ty::U64 },
            left,
            right,
        );
        function.ret(vec![value, flag]);
        function.build();
        let module = builder.build().unwrap();
        assert_eq!((fid, bid), (FuncId::new(0), BlockId::new(0)));
        let reflected = reflect_core_module_v1(&module, &[(fid, 4096)]).unwrap();
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let entry = catalog.entry(fid).unwrap();
        let site = catalog
            .fetch(Coordinate {
                function: fid,
                block: bid,
                instruction: 0,
            })
            .unwrap();
        let returning = catalog
            .fetch(Coordinate {
                function: fid,
                block: bid,
                instruction: 1,
            })
            .unwrap();
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let arguments = list("IRScalar", &[scalar(nat(a)), scalar(nat(b))]);
        let initial = app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(0),
                arguments.clone(),
                memory(),
                nat(37),
            ],
        );
        let memory_guard = truth(&mut assembler, EntryTarget::memory_admission(memory()));
        let entry_guard = truth(
            &mut assembler,
            entry.admission(&model, arguments.clone()).unwrap(),
        );
        let initialized = entry
            .initialize(
                &mut assembler,
                &model,
                arguments,
                memory(),
                nat(37),
                memory_guard,
                entry_guard,
            )
            .unwrap();
        let current = initialized.current();
        let nominal = app(if signed { "IRTy.int_" } else { "IRTy.uint_" }, [nat(64)]);
        let left = assembler
            .conversion(
                c("IRScalar"),
                app("ir_getd", [current.machine(), nat(0)]),
                scalar(nat(a)),
            )
            .unwrap();
        let right = assembler
            .conversion(
                c("IRScalar"),
                app("ir_getd", [current.machine(), nat(1)]),
                scalar(nat(b)),
            )
            .unwrap();
        let left_fits = truth(
            &mut assembler,
            app("ir_byte_integer_fits_v1", [nominal.clone(), nat(a)]),
        );
        let right_fits = truth(
            &mut assembler,
            app("ir_byte_integer_fits_v1", [nominal.clone(), nat(b)]),
        );
        let result_types = truth(
            &mut assembler,
            app(
                "ir_byte_ty_list_eq_v1",
                [
                    app("ir_byte_site_results_v1", [site.site.clone()]),
                    list("IRTy", &[nominal, c("IRTy.bool_")]),
                ],
            ),
        );
        let transferred = site
            .overflow(
                &mut assembler,
                &model,
                current,
                [nat(a), nat(b)],
                OverflowPremises {
                    left,
                    right,
                    left_fits,
                    right_fits,
                    result_types,
                    before: initialized.valid().clone(),
                },
            )
            .unwrap();
        let (word, equality, output_bound) = assembler
            .byte_add_word64_canonical(nat(a), nat(b), bounded(a), bounded(b))
            .unwrap();
        assert_eq!(word, raw(nat(a), nat(b)));
        replay(
            assembler.local_scope(),
            &[],
            output_bound.term(),
            &bound(raw(nat(a), nat(b))),
            &["ir_byte_add_word_bound_v1"],
        );
        // Transport the ORIGINAL full result guard through raw=FAST. The Bool
        // lane remains the actual opcode's expression, never assumed false.
        let flag = transferred.values()[1].clone();
        let guard_body = site
            .value_binding_check(&model, &[scalar(Expr::bvar(0)), flag.clone()])
            .unwrap();
        let guard_function = Expr::lam(BinderInfo::Default, c("Nat"), guard_body);
        let guarded = assembler
            .congruence_function(equality.clone(), c("Bool"), guard_function)
            .unwrap();
        let guard_fast = truth(&mut assembler, guarded.right().clone());
        let guard = assembler.compose(guarded, guard_fast).unwrap();
        let guard = assembler
            .convert_endpoints(
                guard,
                site.value_binding_check(&model, transferred.values())
                    .unwrap(),
                c("Bool.true"),
            )
            .unwrap();
        let binding = site
            .bind_values(
                &mut assembler,
                &model,
                current,
                transferred.values(),
                ValueBindingPremises {
                    result: guard,
                    before: initialized.valid().clone(),
                },
            )
            .unwrap();
        let run = binding
            .complete_run(&mut assembler, transferred.run().clone())
            .unwrap();
        assert_eq!(run.fuel().term(), NatTerm::literal(1).term());
        let next_word = |word: Expr| Current {
            frame: app(
                "ir_frame_advance",
                [app(
                    "ir_frame_set_many",
                    [
                        current.frame.clone(),
                        site.results.clone(),
                        list("IRScalar", &[scalar(word), flag.clone()]),
                    ],
                )],
            ),
            ..current.clone()
        };
        let frame_function = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            next_word(Expr::bvar(0)).running(&model),
        );
        let mapped = assembler
            .congruence_function(equality, model.config_type(), frame_function)
            .unwrap();
        let fast_next = next_word(fast(nat(a), nat(b)));
        let mapped = assembler
            .convert_endpoints(mapped, run.reached().clone(), fast_next.running(&model))
            .unwrap();
        let prefix = assembler.compose(run.equality().clone(), mapped).unwrap();
        let (answer, expected_flag) = if signed {
            let (answer, flag) = (a as i64).overflowing_add(b as i64);
            (answer as u64, flag)
        } else {
            a.overflowing_add(b)
        };
        let next = Current {
            frame: app(
                "ir_frame_advance",
                [app(
                    "ir_frame_set_many",
                    [
                        current.frame.clone(),
                        list("Nat", &[nat(2), nat(3)]),
                        list("IRScalar", &[scalar(nat(answer)), boolean(expected_flag)]),
                    ],
                )],
            ),
            ..current.clone()
        };
        let prefix = assembler
            .convert_endpoints(
                prefix,
                model.run(&NatTerm::literal(1), current.running(&model)),
                next.running(&model),
            )
            .unwrap();
        let prefix = ExactRun::candidate(
            model.clone(),
            current.running(&model),
            next.running(&model),
            NatTerm::literal(1),
            prefix,
        )
        .unwrap();
        let valid = assembler
            .convert_endpoints(binding.valid().clone(), next.valid(&model), c("Bool.true"))
            .unwrap();
        let returned = returning
            .step(&mut assembler, &model, &next, valid)
            .unwrap();
        let terminal_world = |host: u64| {
            app(
                "IRByteWorldV1.mk",
                [c("Nat"), memory(), nat(host), list("Nat", &[]), nat(9)],
            )
        };
        let terminal = |flag: bool, host: u64| {
            app(
                "IRByteConfigV1.halted",
                [
                    c("Nat"),
                    app(
                        "IROutcome.ret",
                        [list("IRScalar", &[scalar(nat(answer)), boolean(flag)])],
                    ),
                    terminal_world(host),
                ],
            )
        };
        let reduced = assembler
            .conversion(
                model.config_type(),
                returned.right().clone(),
                terminal(expected_flag, 37),
            )
            .unwrap();
        let returned = assembler.compose(returned, reduced).unwrap();
        let tail = assembler
            .one_step(&model, next.running(&model), returned)
            .unwrap();
        let execution = assembler.concatenate(prefix, tail).unwrap();
        assert_eq!(execution.fuel().term(), &app("Nat.add", [nat(1), nat(1)]));
        let mapped = assembler
            .congruence(
                initialized.equality().clone(),
                model.config_type(),
                |state| model.run(execution.fuel(), state),
            )
            .unwrap();
        let mapped = assembler
            .convert_endpoints(
                mapped,
                model.run(&NatTerm::literal(2), initial.clone()),
                execution.equality().left().clone(),
            )
            .unwrap();
        let complete = assembler
            .compose(mapped, execution.equality().clone())
            .unwrap();
        let goal = eq(
            model.config_type(),
            model.run(&NatTerm::literal(2), initial.clone()),
            terminal(expected_flag, 37),
        );
        let operation_root = if signed {
            "ir_byte_step_overflow_int_v1"
        } else {
            "ir_byte_step_overflow_uint_v1"
        };
        replay(
            assembler.local_scope(),
            &[],
            complete.term(),
            &goal,
            &["ir_byte_add_wrap_bounded_sum_v1", operation_root],
        );
        for (flag, host) in [(!expected_flag, 37), (expected_flag, 38)] {
            refuse(
                assembler.local_scope(),
                &[],
                complete.term(),
                &eq(
                    model.config_type(),
                    model.run(&NatTerm::literal(2), initial.clone()),
                    terminal(flag, host),
                ),
            );
        }
    }
}
