// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
use super::*;
use crate::{ModuleBuilder, scoped_local::LocalScope, semantic_evaluation};
use clean_kernel::{Environment, TypeChecker};
use trust_ir::Constant;

#[path = "tests/entry.rs"]
mod entry_tests;
#[path = "tests/ranked.rs"]
mod ranked_tests;

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn ptypes(n: usize) -> Vec<Expr> {
    vec![c("Bool"); n]
}
fn packed(values: &[Expr]) -> Expr {
    values
        .iter()
        .enumerate()
        .rev()
        .fold(c("Unit.unit"), |tail, (i, value)| {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Prod.mk"),
                    vec![Level::zero(), Level::zero()],
                ),
                [
                    c("Bool"),
                    lanes(&ptypes(values.len() - i - 1)),
                    value.clone(),
                    tail,
                ],
            )
        })
}
fn sum_type() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Sum"), vec![Level::zero(), Level::zero()]),
        [lanes(&ptypes(4)), lanes(&ptypes(2))],
    )
}
fn types() -> ImageTypes {
    ImageTypes {
        state: c("Nat"),
        error: c("Bool"),
        value: sum_type(),
        answer: c("Nat"),
    }
}
fn primitive_types() -> ImageTypes {
    ImageTypes {
        value: lanes(&ptypes(3)),
        ..types()
    }
}

fn pure<L: ScopedLocalAllocator>(
    scope: &mut L,
    types: &ImageTypes,
    value: Expr,
) -> CutImageCandidate {
    let run = app(
        semantic_evaluation::PURE,
        [
            types.state.clone(),
            types.error.clone(),
            types.value.clone(),
            value,
        ],
    );
    from_run(scope, types, run)
}
fn from_run<L: ScopedLocalAllocator>(
    scope: &mut L,
    types: &ImageTypes,
    run: Expr,
) -> CutImageCandidate {
    let cps = app(
        TO_CPS,
        [
            types.state.clone(),
            types.error.clone(),
            types.value.clone(),
            types.answer.clone(),
            run.clone(),
        ],
    );
    let s = scope.allocate_local(types.state.clone()).unwrap();
    let ok = scope
        .allocate_local(Expr::arrow(
            types.state.clone(),
            Expr::arrow(types.value.clone(), types.answer.clone()),
        ))
        .unwrap();
    let err = scope
        .allocate_local(Expr::arrow(
            types.state.clone(),
            Expr::arrow(types.error.clone(), types.answer.clone()),
        ))
        .unwrap();
    let observed = Expr::apps(
        cps.clone(),
        [s.term().clone(), ok.term().clone(), err.term().clone()],
    );
    let proof = lams(
        &[s, ok, err],
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [types.answer.clone(), observed],
        ),
    );
    CutImageCandidate { run, cps, proof }
}

struct Model {
    provider: FuncId,
    run: Expr,
    cps: Expr,
    proof: Expr,
    forged: bool,
}
impl CutImageModel for Model {
    fn original(&self, m: &Module, f: &Function) -> Result<()> {
        if m.completeness.is_some()
            || !m.imports.is_empty()
            || !m.globals.is_empty()
            || !f.proofs.is_empty()
            || !f.attrs.is_empty()
            || f.summary.is_some()
            || f.body_gate.is_some()
            || f.blocks
                .iter()
                .flat_map(|b| &b.body)
                .any(|n| !n.proofs.is_empty() || n.proof_context.is_some())
        {
            return Err("ordinary test model has no annotation/table meaning".into());
        }
        Ok(())
    }
    fn value_type(&self, _: &Module, ty: &Ty) -> Result<Expr> {
        if *ty == Ty::Bool {
            Ok(c("Bool"))
        } else {
            Err("ordinary model only has Bool SSA lanes".into())
        }
    }
    fn instruction<L: ScopedLocalAllocator>(
        &self,
        scope: &mut L,
        site: &CutSite<'_>,
        operands: &[CutValue],
        result_types: &[Expr],
        types: &ImageTypes,
    ) -> Result<CutImageCandidate> {
        let actual = ImageTypes {
            value: lanes(result_types),
            ..types.clone()
        };
        match &site.node.inst {
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(value),
            } => Ok(pure(
                scope,
                &actual,
                packed(&[c(if *value { "Bool.true" } else { "Bool.false" })]),
            )),
            Inst::Call { callee, args }
                if *callee == self.provider
                    && args.len() == 3
                    && operands.len() == 3
                    && result_types == ptypes(3) =>
            {
                let values = operands.iter().map(|v| v.term.clone()).collect::<Vec<_>>();
                Ok(CutImageCandidate {
                    run: Expr::apps(self.run.clone(), values.clone()),
                    cps: Expr::apps(self.cps.clone(), values.clone()),
                    proof: if self.forged {
                        c("Bool.true")
                    } else {
                        Expr::apps(self.proof.clone(), values)
                    },
                })
            }
            _ => Err("unmodelled original instruction".into()),
        }
    }
    fn continuing<L: ScopedLocalAllocator>(
        &self,
        scope: &mut L,
        _: &CutSite<'_>,
        args: &[CutValue],
        captures: &[CutValue],
        types: &ImageTypes,
    ) -> Result<CutImageCandidate> {
        if args.len() != 3 || captures.len() != 1 {
            return Err("ordinary cut boundary".into());
        }
        let values = args
            .iter()
            .chain(captures)
            .map(|v| v.term.clone())
            .collect::<Vec<_>>();
        let tag = Expr::apps(
            Expr::const_(
                Name::from_string("Sum.inl"),
                vec![Level::zero(), Level::zero()],
            ),
            [lanes(&ptypes(4)), lanes(&ptypes(2)), packed(&values)],
        );
        Ok(pure(scope, types, tag))
    }
    fn returning<L: ScopedLocalAllocator>(
        &self,
        scope: &mut L,
        _: &CutSite<'_>,
        values: &[CutValue],
        types: &ImageTypes,
    ) -> Result<CutImageCandidate> {
        if values.len() != 2 {
            return Err("ordinary original return arity".into());
        }
        let values = values.iter().map(|v| v.term.clone()).collect::<Vec<_>>();
        let tag = Expr::apps(
            Expr::const_(
                Name::from_string("Sum.inr"),
                vec![Level::zero(), Level::zero()],
            ),
            [lanes(&ptypes(4)), lanes(&ptypes(2)), packed(&values)],
        );
        Ok(pure(scope, types, tag))
    }
}

struct Graph {
    module: Module,
    function: FuncId,
    provider: FuncId,
    header: BlockId,
    back: BlockId,
    failed: BlockId,
    cursor: ValueId,
    accumulator: ValueId,
    world: ValueId,
}
fn graph() -> Graph {
    let mut m = ModuleBuilder::new_with_target_info(
        "ordinary_cut",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let provider_ty = m.add_func_type(vec![Ty::Bool; 3], vec![Ty::Bool; 3]);
    let provider = m.declare_function("ordinary_provider", provider_ty);
    let ty = m.add_func_type(vec![Ty::Bool; 4], vec![Ty::Bool; 2]);
    let mut f = m.function("ordinary_fold", ty);
    let entry = f.create_block();
    let header = f.create_block();
    let body = f.create_block();
    let back = f.create_block();
    let done = f.create_block();
    let failed = f.create_block();
    let initial = (0..4)
        .map(|_| f.add_block_param(entry, Ty::Bool))
        .collect::<Vec<_>>();
    let cursor = f.add_block_param(header, Ty::Bool);
    let accumulator = f.add_block_param(header, Ty::Bool);
    let world = f.add_block_param(header, Ty::Bool);
    f.switch_to_block(entry);
    f.br(header, initial[1..].to_vec());
    f.switch_to_block(header);
    f.condbr(cursor, body, vec![], done, vec![]);
    f.switch_to_block(body);
    let [new_world, new_accumulator, normal] =
        f.call_results(provider, vec![initial[0], world, accumulator]);
    f.condbr(normal, back, vec![], failed, vec![]);
    f.switch_to_block(back);
    let next = f.const_value(Ty::Bool, Constant::Bool(false));
    f.br(header, vec![next, new_accumulator, new_world]);
    f.switch_to_block(done);
    f.ret(vec![accumulator, world]);
    f.switch_to_block(failed);
    f.ret(vec![new_accumulator, new_world]);
    let function = f.build();
    Graph {
        module: m.build().unwrap(),
        function,
        provider,
        header,
        back,
        failed,
        cursor,
        accumulator,
        world,
    }
}

fn model(scope: &mut LocalScope, provider: FuncId) -> (Model, Vec<ScopedLocal>) {
    let p = primitive_types();
    let run_ty = app(
        semantic_evaluation::RUN,
        [p.state.clone(), p.error.clone(), p.value.clone()],
    );
    let arrows = |body| (0..3).fold(body, |body, _| Expr::arrow(c("Bool"), body));
    let run = scope.allocate_local(arrows(run_ty)).unwrap();
    let cps = scope.allocate_local(arrows(cps_type(&p))).unwrap();
    let values = (0..3)
        .map(|_| scope.allocate_local(c("Bool")).unwrap())
        .collect::<Vec<_>>();
    let args = values.iter().map(|v| v.term().clone()).collect::<Vec<_>>();
    let proposition = image(
        &p,
        Expr::apps(run.term().clone(), args.clone()),
        Expr::apps(cps.term().clone(), args),
    );
    let proposition = values
        .iter()
        .rev()
        .fold(proposition, |body, local| local.pi(body));
    let proof = scope.allocate_local(proposition).unwrap();
    (
        Model {
            provider,
            run: run.term().clone(),
            cps: cps.term().clone(),
            proof: proof.term().clone(),
            forged: false,
        },
        vec![run, cps, proof],
    )
}
fn environment() -> Environment {
    let mut env = semantic_evaluation::build_environment().unwrap();
    semantic_evaluation::install_handle_into(&mut env).unwrap();
    env.init_unit().unwrap();
    env.init_sum().unwrap();
    env.init_nat().unwrap();
    env
}
fn close(scope: &LocalScope, params: &[ScopedLocal], term: Expr, proof: bool) -> Expr {
    scope
        .close(&params.iter().rev().fold(term, |term, local| {
            if proof {
                local.lam(term)
            } else {
                local.pi(term)
            }
        }))
        .unwrap()
}
fn build(g: &Graph, forged: bool) -> (Expr, Expr) {
    let mut scope = LocalScope::new();
    let (mut model, mut params) = model(&mut scope, g.provider);
    model.forged = forged;
    let report = crate::validate_module_report(&g.module);
    assert!(report.is_ok(), "{:?}", report.errors());
    let endpoint = CutImageEndpoint::new(&report, g.function, g.header).unwrap();
    let candidate = endpoint
        .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
        .unwrap();
    assert_eq!(candidate.parameters.len(), 4);
    assert_eq!(candidate.ids[..3], [g.cursor, g.accumulator, g.world]);
    params.extend(candidate.parameters);
    let claim = close(
        &scope,
        &params,
        candidate.candidate.proposition(&types()),
        false,
    );
    let proof = close(&scope, &params, candidate.candidate.proof, true);
    (claim, proof)
}
fn check(env: &Environment, claim: &Expr, proof: &Expr) -> Result<()> {
    let mut tc = TypeChecker::new(env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.set_heartbeat_limit(5_000_000);
    tc.set_max_cache_entries(16_384);
    let result = tc
        .check_type(claim, &Expr::sort(Level::zero()))
        .map_err(|e| format!("claim {e}"))
        .and_then(|_| {
            tc.check_type(proof, claim)
                .map_err(|e| format!("proof {e}"))
        });
    assert!(
        !tc.heartbeat_spent(),
        "a replay budget stop cannot qualify an endpoint refusal"
    );
    result
}

#[test]
fn ordinary_typed_provider_cut_composes_actual_edges_and_explicit_image_premise() {
    let g = graph();
    let (claim, proof) = build(&g, false);
    let env = environment();
    check(&env, &claim, &proof).unwrap();
    let audit = env.audit_certification(&claim, &proof);
    assert!(audit.is_certified(), "{audit:?}");
    for name in audit.dependencies {
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        assert!(env.trust_marker_deps(&name).unwrap().is_empty());
    }
    // The analysis sink has three lanes while the actual function returns two.
    let cut = NaturalLoopCut::new(&g.module.functions[1], g.header).unwrap();
    assert!(
        matches!(cut.analysis_function().blocks.iter().find(|b| b.id == g.back).unwrap().body.last().unwrap().inst, Inst::Return { ref values } if values.len() == 3)
    );
}

fn conditional_graph(both_arms: bool, back_on_true: bool) -> Graph {
    let mut g = graph();
    let function = g
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == g.function)
        .unwrap();
    let node = function
        .blocks
        .iter_mut()
        .find(|b| b.id == g.back)
        .unwrap()
        .body
        .last_mut()
        .unwrap();
    let Inst::Br { target, args } = &node.inst else {
        panic!("original backedge")
    };
    assert_eq!(*target, g.header);
    let args = args.clone();
    let (other_target, other_args) = if both_arms {
        (g.header, vec![args[0], args[2], args[1]])
    } else {
        (g.failed, vec![])
    };
    node.inst = if back_on_true {
        Inst::CondBr {
            cond: g.cursor,
            then_target: g.header,
            then_args: args,
            else_target: other_target,
            else_args: other_args,
        }
    } else {
        Inst::CondBr {
            cond: g.cursor,
            then_target: other_target,
            then_args: other_args,
            else_target: g.header,
            else_args: args,
        }
    };
    g
}

fn capture_conditional(name: &str, claim: &Expr, proof: &Expr, verdict: &str) {
    if let Some(root) = std::env::var_os("TRUST_IR_CONDITIONAL_CUT_ARTIFACT_DIR") {
        let path = std::path::PathBuf::from(root).join(name);
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(
            path.join("goal.bin"),
            trust_ir::proof::encode_clean_expr_dag_v2(claim).unwrap(),
        )
        .unwrap();
        std::fs::write(
            path.join("proof.bin"),
            trust_ir::proof::encode_clean_expr_dag_v2(proof).unwrap(),
        )
        .unwrap();
        std::fs::write(path.join("verdict.txt"), verdict).unwrap();
    }
}

fn check_conditional(name: &str, env: &Environment, claim: &Expr, proof: &Expr, accepted: bool) {
    let encoded_goal = trust_ir::proof::encode_clean_expr_dag_v2(claim).unwrap();
    let encoded_proof = trust_ir::proof::encode_clean_expr_dag_v2(proof).unwrap();
    let claim = trust_ir::proof::decode_clean_expr_dag_v2(&encoded_goal).unwrap();
    let proof = trust_ir::proof::decode_clean_expr_dag_v2(&encoded_proof).unwrap();
    let mut tc = TypeChecker::new(env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.set_heartbeat_limit(5_000_000);
    tc.set_max_cache_entries(16_384);
    tc.check_type(&claim, &Expr::prop()).unwrap();
    let result = tc.check_type(&proof, &claim);
    let verdict = if accepted {
        result.unwrap();
        let audit = env.audit_certification(&claim, &proof);
        assert!(audit.is_certified(), "{audit:?}");
        for dependency in audit.dependencies {
            assert!(env.axiom_deps(&dependency).unwrap().is_empty());
            assert!(env.trust_marker_deps(&dependency).unwrap().is_empty());
        }
        "kernel and rooted audit accepted; empty axiom/trust-marker closure".to_string()
    } else {
        let error = result.unwrap_err();
        assert!(
            matches!(error, clean_kernel::TypeError::TypeMismatch { .. }),
            "{error:?}"
        );
        format!("semantic TypeMismatch: {error:?}")
    };
    assert!(!tc.heartbeat_spent());
    capture_conditional(name, &claim, &proof, &verdict);
}

#[test]
fn conditional_backedge_images_preserve_both_guard_arms_and_payloads() {
    let env = environment();
    for both in [false, true] {
        let g = conditional_graph(both, true);
        let (claim, proof) = build(&g, false);
        check_conditional(
            &format!("conditional-{both}-then"),
            &env,
            &claim,
            &proof,
            true,
        );
        let changed = conditional_graph(both, false);
        let (changed_claim, changed_proof) = build(&changed, false);
        check_conditional(
            &format!("conditional-{both}-else"),
            &env,
            &changed_claim,
            &changed_proof,
            true,
        );
        check_conditional(
            &format!("conditional-{both}-swapped-stale"),
            &env,
            &changed_claim,
            &proof,
            false,
        );
    }
}

#[test]
fn stale_cursor_accumulator_world_and_failure_return_proofs_refuse() {
    let original = graph();
    let (_, old_proof) = build(&original, false);
    let env = environment();
    for kind in 0..4 {
        let mut changed = graph();
        let old = [changed.cursor, changed.accumulator, changed.world];
        let f = changed
            .module
            .functions
            .iter_mut()
            .find(|f| f.id == changed.function)
            .unwrap();
        let block = if kind < 3 {
            changed.back
        } else {
            changed.failed
        };
        let node = f
            .blocks
            .iter_mut()
            .find(|b| b.id == block)
            .unwrap()
            .body
            .last_mut()
            .unwrap();
        match &mut node.inst {
            Inst::Br { args, .. } => args[kind] = old[kind],
            Inst::Return { values } => values[1] = old[2],
            _ => panic!(),
        }
        let (claim, new_proof) = build(&changed, false);
        check(&env, &claim, &new_proof).unwrap();
        assert!(
            check(&env, &claim, &old_proof).is_err(),
            "stale endpoint {kind}"
        );
    }
}

#[test]
fn image_wrappers_do_not_authorize_a_forged_provider_image() {
    let (claim, proof) = build(&graph(), true);
    assert!(check(&environment(), &claim, &proof).is_err());
}

#[test]
fn invalid_original_and_structural_limits_refuse_before_image_assembly() {
    let mut g = graph();
    let f = g
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == g.function)
        .unwrap();
    f.blocks
        .iter_mut()
        .find(|b| b.id == g.failed)
        .unwrap()
        .body
        .last_mut()
        .unwrap()
        .inst = Inst::Return { values: vec![] };
    let report = crate::validate_module_report(&g.module);
    assert!(!report.is_ok());
    assert!(CutImageEndpoint::new(&report, g.function, g.header).is_err());
    let g = graph();
    let report = crate::validate_module_report(&g.module);
    let endpoint = CutImageEndpoint::new(&report, g.function, g.header).unwrap();
    for limits in [
        CutImageLimits {
            operations: 1,
            ..CutImageLimits::default()
        },
        CutImageLimits {
            depth: 1,
            ..CutImageLimits::default()
        },
        CutImageLimits {
            lanes: 1,
            ..CutImageLimits::default()
        },
    ] {
        let mut scope = LocalScope::new();
        let (model, _) = model(&mut scope, g.provider);
        assert!(
            endpoint
                .reconstruct(&model, &mut scope, types(), limits)
                .is_err()
        );
    }
}

#[test]
fn conditional_backedge_and_block_storage_order_preserve_checked_images() {
    let original = graph();
    let (_, proof) = build(&original, false);
    let mut reordered = graph();
    reordered
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == reordered.function)
        .unwrap()
        .blocks
        .reverse();
    let (claim, _) = build(&reordered, false);
    check(&environment(), &claim, &proof).unwrap();
    let mut changed = graph();
    let f = changed
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == changed.function)
        .unwrap();
    let node = f
        .blocks
        .iter_mut()
        .find(|b| b.id == changed.back)
        .unwrap()
        .body
        .last_mut()
        .unwrap();
    let Inst::Br { args, .. } = &node.inst else {
        panic!()
    };
    node.inst = Inst::CondBr {
        cond: changed.cursor,
        then_target: changed.header,
        then_args: args.clone(),
        else_target: changed.failed,
        else_args: vec![],
    };
    let report = crate::validate_module_report(&changed.module);
    assert!(report.is_ok(), "{:?}", report.errors());
    let (changed_claim, changed_proof) = build(&changed, false);
    check_conditional(
        "conditional-with-exit",
        &environment(),
        &changed_claim,
        &changed_proof,
        true,
    );
    check_conditional(
        "conditional-with-exit-stale-unconditional",
        &environment(),
        &changed_claim,
        &proof,
        false,
    );
}

#[test]
fn concrete_provider_failure_keeps_the_updated_full_world() {
    let g = graph();
    let mut scope = LocalScope::new();
    let p = primitive_types();
    let parameters = (0..3)
        .map(|_| scope.allocate_local(c("Bool")).unwrap())
        .collect::<Vec<_>>();
    let state = scope.allocate_local(c("Nat")).unwrap();
    let outcome_ty = Expr::apps(
        Expr::const_(
            Name::from_string("Except"),
            vec![Level::zero(), Level::zero()],
        ),
        [p.error.clone(), p.value.clone()],
    );
    let failure = Expr::apps(
        Expr::const_(
            Name::from_string("Except.error"),
            vec![Level::zero(), Level::zero()],
        ),
        [p.error.clone(), p.value.clone(), c("Bool.true")],
    );
    let updated = Expr::apps(
        Expr::const_(
            Name::from_string("Prod.mk"),
            vec![Level::zero(), Level::zero()],
        ),
        [
            p.state.clone(),
            outcome_ty,
            Expr::app(c("Nat.succ"), state.term().clone()),
            failure,
        ],
    );
    let run = state.lam(updated);
    let image = from_run(&mut scope, &p, run.clone());
    let model = Model {
        provider: g.provider,
        run: lams(&parameters, run),
        cps: lams(&parameters, image.cps),
        proof: lams(&parameters, image.proof),
        forged: false,
    };
    let report = crate::validate_module_report(&g.module);
    let endpoint = CutImageEndpoint::new(&report, g.function, g.header).unwrap();
    let cut = endpoint
        .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
        .unwrap();
    let claim = close(
        &scope,
        &cut.parameters,
        cut.candidate.proposition(&types()),
        false,
    );
    let proof = close(&scope, &cut.parameters, cut.candidate.proof, true);
    let env = environment();
    check(&env, &claim, &proof).unwrap();
    let run = scope
        .close(&lams(&cut.parameters, cut.candidate.run))
        .unwrap();
    let actual = Expr::apps(
        run,
        [
            c("Bool.true"),
            c("Bool.false"),
            c("Bool.false"),
            c("Bool.true"),
            Expr::nat_lit(7),
        ],
    );
    let outcome_ty = Expr::apps(
        Expr::const_(
            Name::from_string("Except"),
            vec![Level::zero(), Level::zero()],
        ),
        [types().error, types().value],
    );
    let failure = Expr::apps(
        Expr::const_(
            Name::from_string("Except.error"),
            vec![Level::zero(), Level::zero()],
        ),
        [types().error, types().value, c("Bool.true")],
    );
    let expected = Expr::apps(
        Expr::const_(
            Name::from_string("Prod.mk"),
            vec![Level::zero(), Level::zero()],
        ),
        [c("Nat"), outcome_ty.clone(), Expr::nat_lit(8), failure],
    );
    let result_ty = product(c("Nat"), outcome_ty);
    let claim = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [result_ty.clone(), actual, expected.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [result_ty, expected],
    );
    check(&env, &claim, &proof).unwrap();
}

fn capture_graph(second: bool) -> Graph {
    let mut g = graph();
    let f = g
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == g.function)
        .unwrap();
    let entry = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
    let capture = entry.params[usize::from(second)].0;
    for block in &mut f.blocks {
        for node in &mut block.body {
            if let Inst::Call { args, .. } = &mut node.inst {
                args[0] = g.cursor;
            }
        }
        if block.id == g.back {
            let Inst::Br { args, .. } = &mut block.body.last_mut().unwrap().inst else {
                panic!()
            };
            args[2] = capture;
        }
    }
    g
}

#[test]
fn alpha_equivalent_images_still_require_the_exact_original_boundary_map() {
    let a = capture_graph(false);
    let b = capture_graph(true);
    let (claim_a, proof_a) = build(&a, false);
    let (claim_b, _) = build(&b, false);
    // This valid universal image reuse MUST NOT be mistaken for an unchanged
    // source/SSA map. Full entry/source correspondence remains a separate claim.
    assert_eq!(claim_a, claim_b);
    check(&environment(), &claim_b, &proof_a).unwrap();
    let ra = crate::validate_module_report(&a.module);
    let rb = crate::validate_module_report(&b.module);
    let ea = CutImageEndpoint::new(&ra, a.function, a.header).unwrap();
    let eb = CutImageEndpoint::new(&rb, b.function, b.header).unwrap();
    let mut scope = LocalScope::new();
    let (model, globals) = model(&mut scope, a.provider);
    let ca = ea
        .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
        .unwrap();
    let cb = eb
        .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
        .unwrap();
    assert_ne!(ca.ids, cb.ids);
    let bindings = |ids: &[ValueId]| {
        ids.iter()
            .map(|id| CutValue {
                id: *id,
                ty: Ty::Bool,
                term: c("Bool.true"),
            })
            .collect::<Vec<_>>()
    };
    assert!(eb.at_boundary(&ca, &bindings(&ca.ids)).is_err());
    assert!(eb.at_boundary(&cb, &bindings(&ca.ids)).is_err());
    let instantiated = eb.at_boundary(&cb, &bindings(&cb.ids)).unwrap();
    let claim = close(&scope, &globals, instantiated.proposition(&types()), false);
    let proof = close(&scope, &globals, instantiated.proof, true);
    check(&environment(), &claim, &proof).unwrap();
    let mut duplicate = bindings(&cb.ids);
    duplicate[3] = duplicate[0].clone();
    assert!(eb.at_boundary(&cb, &duplicate).is_err());
    let mut wrong_type = bindings(&cb.ids);
    wrong_type[3].ty = Ty::I64;
    assert!(eb.at_boundary(&cb, &wrong_type).is_err());
    let mut self_parameter = bindings(&cb.ids);
    self_parameter[0].term = cb.parameters[0].term().clone();
    assert!(eb.at_boundary(&cb, &self_parameter).is_err());
}

#[test]
fn changed_branch_and_provider_operands_refuse_the_old_complete_image() {
    let original = graph();
    let (_, proof) = build(&original, false);
    let env = environment();
    for mode in 0..3 {
        let mut g = graph();
        let f = g
            .module
            .functions
            .iter_mut()
            .find(|f| f.id == g.function)
            .unwrap();
        if mode == 0 {
            let node = f
                .blocks
                .iter_mut()
                .find(|b| b.id == g.header)
                .unwrap()
                .body
                .last_mut()
                .unwrap();
            let Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } = &mut node.inst
            else {
                panic!()
            };
            std::mem::swap(then_target, else_target);
            std::mem::swap(then_args, else_args);
        } else {
            let block = f
                .blocks
                .iter_mut()
                .find(|b| b.body.iter().any(|n| matches!(n.inst, Inst::Call { .. })))
                .unwrap();
            if mode == 1 {
                let Inst::Call { args, .. } = &mut block.body[0].inst else {
                    panic!()
                };
                args[1] = g.accumulator;
            } else {
                let Inst::CondBr { cond, .. } = &mut block.body.last_mut().unwrap().inst else {
                    panic!()
                };
                *cond = g.cursor;
            }
        }
        let (claim, fresh) = build(&g, false);
        check(&env, &claim, &fresh).unwrap();
        assert!(
            check(&env, &claim, &proof).is_err(),
            "changed branch/provider operand {mode}"
        );
    }
    let mut g = graph();
    let declaration = &g.module.functions[0];
    let foreign = FuncId(2);
    let ty = declaration.ty;
    g.module
        .functions
        .push(Function::new(foreign, "foreign_provider", ty, BlockId(0)));
    let f = g
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == g.function)
        .unwrap();
    for node in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = foreign;
        }
    }
    let report = crate::validate_module_report(&g.module);
    assert!(report.is_ok(), "{:?}", report.errors());
    let endpoint = CutImageEndpoint::new(&report, g.function, g.header).unwrap();
    let mut scope = LocalScope::new();
    let (model, _) = model(&mut scope, g.provider);
    assert!(
        endpoint
            .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
            .is_err()
    );
}

fn parameterized_edge_graph(swap: bool) -> Graph {
    let mut g = graph();
    let f = g
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == g.function)
        .unwrap();
    let last = f
        .blocks
        .iter()
        .flat_map(|b| {
            b.params
                .iter()
                .map(|(id, _)| *id)
                .chain(b.body.iter().flat_map(|n| n.results.iter().copied()))
        })
        .map(|id| id.0)
        .max()
        .unwrap();
    let world = ValueId(last + 1);
    let accumulator = ValueId(last + 2);
    let call = f
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .find(|n| matches!(n.inst, Inst::Call { .. }))
        .unwrap();
    let arguments = if swap {
        vec![call.results[1], call.results[0]]
    } else {
        vec![call.results[0], call.results[1]]
    };
    for block in &mut f.blocks {
        if block.id == g.back {
            block.params = vec![(world, Ty::Bool), (accumulator, Ty::Bool)];
            let Inst::Br { args, .. } = &mut block.body.last_mut().unwrap().inst else {
                panic!()
            };
            args[1] = accumulator;
            args[2] = world;
        } else if let Inst::CondBr {
            then_target,
            then_args,
            ..
        } = &mut block.body.last_mut().unwrap().inst
        {
            if *then_target == g.back {
                *then_args = arguments.clone();
            }
        }
    }
    g
}

#[test]
fn parameterized_intermediate_edges_keep_all_original_argument_bindings() {
    let (claim, proof) = build(&parameterized_edge_graph(false), false);
    let env = environment();
    check(&env, &claim, &proof).unwrap();
    let (changed, fresh) = build(&parameterized_edge_graph(true), false);
    check(&env, &changed, &fresh).unwrap();
    assert!(check(&env, &changed, &proof).is_err());
}
