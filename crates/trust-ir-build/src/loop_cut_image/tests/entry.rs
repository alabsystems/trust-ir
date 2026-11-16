// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
use super::*;
use std::cell::RefCell;

fn two(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero(), Level::zero()]),
        args,
    )
}

struct PrefixGraph {
    g: Graph,
    entry: BlockId,
    route: BlockId,
    inputs: Vec<ValueId>,
    computed: Vec<ValueId>,
}
fn prefix_graph(cyclic: bool) -> PrefixGraph {
    let mut m = ModuleBuilder::new_with_target_info(
        "entry_image",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let pty = m.add_func_type(vec![Ty::Bool; 3], vec![Ty::Bool; 3]);
    let provider = m.declare_function("ordinary_entry_provider", pty);
    let ty = m.add_func_type(vec![Ty::Bool; 4], vec![Ty::Bool; 2]);
    let mut f = m.function("ordinary_entry", ty);
    let entry = f.create_block();
    let route = f.create_block();
    let again = cyclic.then(|| f.create_block());
    let header = f.create_block();
    let body = f.create_block();
    let back = f.create_block();
    let done = f.create_block();
    let failed = f.create_block();
    let inputs = (0..4)
        .map(|_| f.add_block_param(entry, Ty::Bool))
        .collect::<Vec<_>>();
    let rworld = f.add_block_param(route, Ty::Bool);
    let racc = f.add_block_param(route, Ty::Bool);
    let cursor = f.add_block_param(header, Ty::Bool);
    let accumulator = f.add_block_param(header, Ty::Bool);
    let world = f.add_block_param(header, Ty::Bool);
    let failure = f.add_block_param(failed, Ty::Bool);
    let failure_world = f.add_block_param(failed, Ty::Bool);
    f.switch_to_block(entry);
    let [new_world, new_acc, normal] = f.call_results(provider, inputs[..3].to_vec());
    f.condbr(
        normal,
        route,
        vec![new_world, new_acc],
        failed,
        vec![new_acc, new_world],
    );
    f.switch_to_block(route);
    f.condbr(
        inputs[3],
        again.unwrap_or(header),
        if cyclic {
            vec![]
        } else {
            vec![inputs[1], racc, rworld]
        },
        header,
        vec![inputs[1], rworld, racc],
    );
    if let Some(again) = again {
        f.switch_to_block(again);
        f.br(route, vec![rworld, racc]);
    }
    f.switch_to_block(header);
    f.condbr(cursor, body, vec![], done, vec![]);
    f.switch_to_block(body);
    // This capture is COMPUTED by the prefix call, not an entry parameter.
    f.condbr(normal, back, vec![], done, vec![]);
    f.switch_to_block(back);
    let next = f.const_value(Ty::Bool, Constant::Bool(false));
    f.br(header, vec![next, accumulator, world]);
    f.switch_to_block(done);
    f.ret(vec![accumulator, world]);
    f.switch_to_block(failed);
    f.ret(vec![failure, failure_world]);
    let function = f.build();
    PrefixGraph {
        g: Graph {
            module: m.build().unwrap(),
            function,
            provider,
            header,
            back,
            failed,
            cursor,
            accumulator,
            world,
        },
        entry,
        route,
        inputs,
        computed: vec![new_world, new_acc, normal],
    }
}

type EntryArrival = (Option<EntryHeaderEdge>, Vec<ValueId>, Vec<ValueId>);

struct EntryModel {
    inner: Model,
    arrivals: RefCell<Vec<EntryArrival>>,
    instructions: RefCell<Vec<(BlockId, usize)>>,
}
impl EntryModel {
    fn new(inner: Model) -> Self {
        Self {
            inner,
            arrivals: RefCell::new(vec![]),
            instructions: RefCell::new(vec![]),
        }
    }
}
impl CutImageModel for EntryModel {
    fn original(&self, m: &Module, f: &Function) -> Result<()> {
        self.inner.original(m, f)
    }
    fn value_type(&self, m: &Module, ty: &Ty) -> Result<Expr> {
        self.inner.value_type(m, ty)
    }
    fn instruction<L: ScopedLocalAllocator>(
        &self,
        locals: &mut L,
        site: &CutSite<'_>,
        operands: &[CutValue],
        result_types: &[Expr],
        types: &ImageTypes,
    ) -> Result<CutImageCandidate> {
        self.instructions
            .borrow_mut()
            .push((site.block, site.instruction));
        self.inner
            .instruction(locals, site, operands, result_types, types)
    }
    fn entering<L: ScopedLocalAllocator>(
        &self,
        locals: &mut L,
        boundary: &EntryHeaderBoundary<'_>,
        types: &ImageTypes,
    ) -> Result<CutImageCandidate> {
        let arm = match &boundary.arrival {
            EntryHeaderArrival::FunctionEntry => None,
            EntryHeaderArrival::Edge { site, arm } => {
                assert!(std::ptr::eq(site.module, boundary.module));
                assert!(std::ptr::eq(site.function, boundary.function));
                Some(*arm)
            }
        };
        self.arrivals.borrow_mut().push((
            arm,
            boundary.arguments.iter().map(|a| a.actual.id).collect(),
            boundary.captures.iter().map(|v| v.id).collect(),
        ));
        let bindings = boundary.bindings();
        assert_eq!(
            bindings.len(),
            boundary.arguments.len() + boundary.captures.len()
        );
        let values = bindings.iter().map(|v| v.term.clone()).collect::<Vec<_>>();
        let tag = Expr::apps(
            Expr::const_(
                Name::from_string("Sum.inl"),
                vec![Level::zero(), Level::zero()],
            ),
            [
                lanes(&ptypes(values.len())),
                lanes(&ptypes(2)),
                packed(&values),
            ],
        );
        Ok(pure(locals, types, tag))
    }
    fn continuing<L: ScopedLocalAllocator>(
        &self,
        locals: &mut L,
        site: &CutSite<'_>,
        args: &[CutValue],
        captures: &[CutValue],
        types: &ImageTypes,
    ) -> Result<CutImageCandidate> {
        self.inner.continuing(locals, site, args, captures, types)
    }
    fn returning<L: ScopedLocalAllocator>(
        &self,
        locals: &mut L,
        site: &CutSite<'_>,
        values: &[CutValue],
        types: &ImageTypes,
    ) -> Result<CutImageCandidate> {
        self.inner.returning(locals, site, values, types)
    }
}

fn build_prefix(g: &PrefixGraph, forged: bool) -> (Expr, Expr) {
    let mut scope = LocalScope::new();
    let (mut inner, mut params) = model(&mut scope, g.g.provider);
    inner.forged = forged;
    let model = EntryModel::new(inner);
    let report = crate::validate_module_report(&g.g.module);
    assert!(report.is_ok(), "{:?}", report.errors());
    let endpoint = EntryCutImageEndpoint::new(&report, g.g.function, g.g.header).unwrap();
    let image = endpoint
        .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
        .unwrap();
    assert_eq!(image.ids, g.inputs);
    assert!(!image.ids.contains(&g.computed[2]));
    assert_eq!(*model.instructions.borrow(), [(g.entry, 0)]);
    let seen = model.arrivals.borrow();
    assert_eq!(seen.len(), 2);
    assert_eq!(seen[0].0, Some(EntryHeaderEdge::Then));
    assert_eq!(seen[1].0, Some(EntryHeaderEdge::Else));
    assert_eq!(seen[0].2.len(), 1);
    params.extend(image.parameters);
    let claim = close(
        &scope,
        &params,
        image.candidate.proposition(&types()),
        false,
    );
    let proof = close(&scope, &params, image.candidate.proof, true);
    (claim, proof)
}

#[test]
fn entry_image_composes_real_provider_computed_capture_and_same_header_arms() {
    let g = prefix_graph(false);
    let (claim, proof) = build_prefix(&g, false);
    let env = environment();
    check(&env, &claim, &proof).unwrap();
    let audit = env.audit_certification(&claim, &proof);
    assert!(audit.is_certified(), "{audit:?}");
    for name in audit.dependencies {
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        assert!(env.trust_marker_deps(&name).unwrap().is_empty());
    }
    let report = crate::validate_module_report(&g.g.module);
    let endpoint = EntryCutImageEndpoint::new(&report, g.g.function, g.g.header).unwrap();
    let mut scope = LocalScope::new();
    let (model, _) = model(&mut scope, g.g.provider);
    assert!(
        endpoint
            .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
            .is_err()
    );

    // The ordinary unconditional incoming edge retains its real capture and
    // never visits the selected loop's provider/body during prefix assembly.
    let direct = graph();
    let report = crate::validate_module_report(&direct.module);
    let endpoint = EntryCutImageEndpoint::new(&report, direct.function, direct.header).unwrap();
    let mut scope = LocalScope::new();
    let (inner, mut params) = super::model(&mut scope, direct.provider);
    let model = EntryModel::new(inner);
    let image = endpoint
        .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
        .unwrap();
    assert!(model.instructions.borrow().is_empty());
    assert_eq!(
        model.arrivals.borrow()[0].0,
        Some(EntryHeaderEdge::Unconditional)
    );
    assert_eq!(model.arrivals.borrow()[0].2.len(), 1);
    params.extend(image.parameters);
    check(
        &env,
        &close(
            &scope,
            &params,
            image.candidate.proposition(&types()),
            false,
        ),
        &close(&scope, &params, image.candidate.proof, true),
    )
    .unwrap();
}

#[test]
fn entry_image_changed_header_arguments_capture_and_provider_proofs_refuse_stale_evidence() {
    let (_, old_proof) = build_prefix(&prefix_graph(false), false);
    let env = environment();
    for mutation in 0..3 {
        let mut g = prefix_graph(false);
        let f =
            g.g.module
                .functions
                .iter_mut()
                .find(|f| f.id == g.g.function)
                .unwrap();
        if mutation < 2 {
            let block = f.blocks.iter_mut().find(|b| b.id == g.route).unwrap();
            let Inst::CondBr {
                then_args,
                else_args,
                ..
            } = &mut block.body.last_mut().unwrap().inst
            else {
                panic!()
            };
            if mutation == 0 {
                then_args.swap(1, 2);
            } else {
                else_args[0] = g.inputs[2];
            }
        } else {
            let block = f.blocks.iter_mut().find(|b| b.id != g.g.header && b.body.last().is_some_and(|n| matches!(n.inst, Inst::CondBr { cond, .. } if cond == g.computed[2])) && b.id != g.entry).unwrap();
            let Inst::CondBr { cond, .. } = &mut block.body.last_mut().unwrap().inst else {
                panic!()
            };
            *cond = g.inputs[3];
        }
        let (claim, proof) = build_prefix(&g, false);
        check(&env, &claim, &proof).unwrap();
        assert!(
            check(&env, &claim, &old_proof).is_err(),
            "stale prefix {mutation}"
        );
    }
    let (claim, proof) = build_prefix(&prefix_graph(false), true);
    assert!(check(&env, &claim, &proof).is_err());
}

#[test]
fn entry_image_nominal_entry_custody_refuses_foreign_maps_and_iteration_role() {
    let g = prefix_graph(false);
    let report = crate::validate_module_report(&g.g.module);
    let entry = EntryCutImageEndpoint::new(&report, g.g.function, g.g.header).unwrap();
    let step = CutImageEndpoint::new(&report, g.g.function, g.g.header).unwrap();
    let mut scope = LocalScope::new();
    let (inner, params) = model(&mut scope, g.g.provider);
    let model = EntryModel::new(inner);
    let mut image = entry
        .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
        .unwrap();
    let bindings = g
        .inputs
        .iter()
        .map(|id| CutValue {
            id: *id,
            ty: Ty::Bool,
            term: c("Bool.true"),
        })
        .collect::<Vec<_>>();
    let instantiated = entry.at_entry(&image, &bindings).unwrap();
    let claim = close(&scope, &params, instantiated.proposition(&types()), false);
    let proof = close(&scope, &params, instantiated.proof, true);
    check(&environment(), &claim, &proof).unwrap();
    let iteration = step
        .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
        .unwrap();
    assert!(
        entry
            .at_entry(&iteration, &bindings)
            .err()
            .unwrap()
            .contains("endpoint role")
    );
    assert!(
        step.at_boundary(&image, &bindings)
            .err()
            .unwrap()
            .contains("endpoint role")
    );
    image.ids.swap(0, 1);
    assert!(entry.at_entry(&image, &bindings).is_err());
    image.ids.swap(0, 1);
    for mutation in 0..4 {
        let mut changed = bindings.clone();
        match mutation {
            0 => {
                changed.pop();
            }
            1 => changed[0].id = changed[1].id,
            2 => changed[0].ty = Ty::U64,
            _ => changed[0].term = image.parameters[0].term().clone(),
        }
        assert!(entry.at_entry(&image, &changed).is_err());
    }
    let foreign = g.g.module.clone();
    let report = crate::validate_module_report(&foreign);
    assert!(
        EntryCutImageEndpoint::new(&report, g.g.function, g.g.header)
            .unwrap()
            .at_entry(&image, &bindings)
            .is_err()
    );
}

#[test]
fn entry_image_refuses_original_invalid_returns_residual_cycles_and_limits() {
    let cyclic = prefix_graph(true);
    let report = crate::validate_module_report(&cyclic.g.module);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert!(CutImageEndpoint::new(&report, cyclic.g.function, cyclic.g.header).is_ok());
    assert!(EntryCutImageEndpoint::new(&report, cyclic.g.function, cyclic.g.header).is_err());
    let g = prefix_graph(false);
    let report = crate::validate_module_report(&g.g.module);
    let endpoint = EntryCutImageEndpoint::new(&report, g.g.function, g.g.header).unwrap();
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
            lanes: 3,
            ..CutImageLimits::default()
        },
    ] {
        let mut scope = LocalScope::new();
        let (inner, _) = model(&mut scope, g.g.provider);
        assert!(
            endpoint
                .reconstruct(&EntryModel::new(inner), &mut scope, types(), limits)
                .is_err()
        );
    }
    let mut invalid = g.g.module.clone();
    let f = invalid
        .functions
        .iter_mut()
        .find(|f| f.id == g.g.function)
        .unwrap();
    for block in &mut f.blocks {
        if block.id != g.g.failed
            && let Inst::Return { values } = &mut block.body.last_mut().unwrap().inst
        {
            values.clear();
        }
    }
    let report = crate::validate_module_report(&invalid);
    assert!(!report.is_ok());
    assert!(EntryCutImageEndpoint::new(&report, g.g.function, g.g.header).is_err());
}

#[test]
fn entry_image_direct_entry_header_stops_without_a_synthetic_site_or_body() {
    let mut m = ModuleBuilder::new_with_target_info(
        "direct_entry",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let pty = m.add_func_type(vec![Ty::Bool; 3], vec![Ty::Bool; 3]);
    let provider = m.declare_function("unused_provider", pty);
    let ty = m.add_func_type(vec![Ty::Bool; 3], vec![Ty::Bool; 2]);
    let mut f = m.function("direct_header", ty);
    let header = f.create_block();
    let body = f.create_block();
    let done = f.create_block();
    let args = (0..3)
        .map(|_| f.add_block_param(header, Ty::Bool))
        .collect::<Vec<_>>();
    f.switch_to_block(header);
    f.condbr(args[0], body, vec![], done, vec![]);
    f.switch_to_block(body);
    let next = f.const_value(Ty::Bool, Constant::Bool(false));
    f.br(header, vec![next, args[1], args[2]]);
    f.switch_to_block(done);
    f.ret(args[1..].to_vec());
    let function = f.build();
    let module = m.build().unwrap();
    let report = crate::validate_module_report(&module);
    assert!(report.is_ok(), "{:?}", report.errors());
    let endpoint = EntryCutImageEndpoint::new(&report, function, header).unwrap();
    let mut scope = LocalScope::new();
    let (inner, mut params) = model(&mut scope, provider);
    let model = EntryModel::new(inner);
    let types = ImageTypes {
        value: Expr::apps(
            Expr::const_(Name::from_string("Sum"), vec![Level::zero(), Level::zero()]),
            [lanes(&ptypes(3)), lanes(&ptypes(2))],
        ),
        ..types()
    };
    let image = endpoint
        .reconstruct(&model, &mut scope, types.clone(), CutImageLimits::default())
        .unwrap();
    assert_eq!(image.ids, args);
    assert_eq!(image.operations, 1);
    assert!(model.instructions.borrow().is_empty());
    assert_eq!(*model.arrivals.borrow(), [(None, args, vec![])]);
    params.extend(image.parameters);
    check(
        &environment(),
        &close(&scope, &params, image.candidate.proposition(&types), false),
        &close(&scope, &params, image.candidate.proof, true),
    )
    .unwrap();
}

// A concrete ordinary provider updates the WHOLE semantic state before either
// returning three SSA lanes or raising an error. No entry/header state is made up.
fn ground_provider(scope: &mut LocalScope, provider: FuncId, mode: u8) -> EntryModel {
    let p = primitive_types();
    let args = (0..3)
        .map(|_| scope.allocate_local(c("Bool")).unwrap())
        .collect::<Vec<_>>();
    let state = scope.allocate_local(c("Nat")).unwrap();
    let outcome_ty = two("Except", [p.error.clone(), p.value.clone()]);
    let observed = if mode == 2 {
        two(
            "Except.error",
            [p.error.clone(), p.value.clone(), c("Bool.true")],
        )
    } else {
        two(
            "Except.ok",
            [
                p.error.clone(),
                p.value.clone(),
                packed(&[
                    c("Bool.false"),
                    c("Bool.true"),
                    c(if mode == 0 { "Bool.true" } else { "Bool.false" }),
                ]),
            ],
        )
    };
    let result = Expr::apps(
        Expr::const_(
            Name::from_string("Prod.mk"),
            vec![Level::zero(), Level::zero()],
        ),
        [
            p.state.clone(),
            outcome_ty,
            Expr::app(c("Nat.succ"), state.term().clone()),
            observed,
        ],
    );
    let run = state.lam(result);
    let image = from_run(scope, &p, run.clone());
    EntryModel::new(Model {
        provider,
        run: lams(&args, run),
        cps: lams(&args, image.cps),
        proof: lams(&args, image.proof),
        forged: false,
    })
}

#[test]
fn entry_image_header_payload_early_return_and_error_keep_the_updated_postworld() {
    let g = prefix_graph(false);
    let report = crate::validate_module_report(&g.g.module);
    let endpoint = EntryCutImageEndpoint::new(&report, g.g.function, g.g.header).unwrap();
    let env = environment();
    for mode in 0..3 {
        let mut scope = LocalScope::new();
        let model = ground_provider(&mut scope, g.g.provider, mode);
        let image = endpoint
            .reconstruct(&model, &mut scope, types(), CutImageLimits::default())
            .unwrap();
        let claim = close(
            &scope,
            &image.parameters,
            image.candidate.proposition(&types()),
            false,
        );
        let proof = close(
            &scope,
            &image.parameters,
            image.candidate.proof.clone(),
            true,
        );
        check(&env, &claim, &proof).unwrap();
        let run = scope
            .close(&lams(&image.parameters, image.candidate.run))
            .unwrap();
        for arm in [false, true] {
            let actual = Expr::apps(
                run.clone(),
                [
                    c("Bool.true"),
                    c("Bool.false"),
                    c("Bool.true"),
                    c(if arm { "Bool.true" } else { "Bool.false" }),
                    Expr::nat_lit(7),
                ],
            );
            let payload = if mode == 0 {
                let values = [
                    c("Bool.false"),
                    c(if arm { "Bool.true" } else { "Bool.false" }),
                    c(if arm { "Bool.false" } else { "Bool.true" }),
                    c("Bool.true"),
                ];
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Sum.inl"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    [lanes(&ptypes(4)), lanes(&ptypes(2)), packed(&values)],
                )
            } else {
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Sum.inr"),
                        vec![Level::zero(), Level::zero()],
                    ),
                    [
                        lanes(&ptypes(4)),
                        lanes(&ptypes(2)),
                        packed(&[c("Bool.true"), c("Bool.false")]),
                    ],
                )
            };
            let outcome = if mode == 2 {
                two(
                    "Except.error",
                    [types().error, types().value, c("Bool.true")],
                )
            } else {
                two("Except.ok", [types().error, types().value, payload])
            };
            let outcome_ty = two("Except", [types().error, types().value]);
            let result_ty = product(c("Nat"), outcome_ty.clone());
            let expected = Expr::apps(
                Expr::const_(
                    Name::from_string("Prod.mk"),
                    vec![Level::zero(), Level::zero()],
                ),
                [c("Nat"), outcome_ty, Expr::nat_lit(8), outcome],
            );
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
    }
}
