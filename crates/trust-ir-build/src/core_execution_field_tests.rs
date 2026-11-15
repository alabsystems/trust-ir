// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual nominal ExtractField replay for two independent symbolic bounded
//! words. The claim is rebuilt from the source instruction and real frame,
//! never copied from the field adapter's returned equality.

use super::*;
use crate::core_reflection::reflect_core_module_v1;
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{
    Block, Endianness, FieldDef, FuncTy, Function, Inst, InstrNode, Module, StructDef, StructId,
    StructPassingPolicy, StructRepr, TargetInfo, Ty,
};

const FUNCTION: FuncId = FuncId(9);
const BLOCK: BlockId = BlockId(7);
const PAIR: StructId = StructId(19);

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .expect("canonical byte vocabulary")
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(1_000_000);
    checker.set_max_cache_entries(100_000);
    checker
}

fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 64,
        max_lookup_candidates: 256,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 100_000,
    }
}

fn fixture() -> Module {
    let mut module = Module::new("symbolic_nominal_field");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module.structs.push(StructDef {
        id: PAIR,
        name: "bounded_status_payload".into(),
        fields: vec![
            FieldDef {
                name: "status".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "payload".into(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    });
    let signature = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Struct(PAIR)],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FUNCTION, "status", signature, BLOCK);
    let mut block = Block::new(BLOCK);
    block.params.push((ValueId(0), Ty::Struct(PAIR)));
    block.body = vec![
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U64,
            aggregate: ValueId(0),
            field: 0,
        })
        .with_result(ValueId(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(1)],
        }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    let errors = crate::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    module
}

fn providers() -> Expr {
    // Real, total, and never called by ExtractField.
    Expr::lam(
        BinderInfo::Default,
        constant("Nat"),
        Expr::lam(
            BinderInfo::Default,
            app("IRList", [constant("IRScalar")]),
            Expr::lam(
                BinderInfo::Default,
                constant("IRByteMemoryV1"),
                Expr::lam(
                    BinderInfo::Default,
                    constant("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            constant("Nat"),
                            app("IROutcome.stuck", [constant("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
}

fn aggregate(first: Expr, second: Expr) -> Expr {
    app(
        "IRScalar.aggv",
        [app(
            "IRScalar.vcons",
            [
                first,
                app("IRScalar.vcons", [second, constant("IRScalar.vnil")]),
            ],
        )],
    )
}

fn current(pair: Expr) -> Current {
    let memory = app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(16), nat(16), nat(8), constant("Bool.true")],
                    ),
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(80), nat(8), nat(0), constant("Bool.true")],
                    ),
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(128), nat(8), nat(7), constant("Bool.false")],
                    ),
                ],
            ),
            Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173))),
            nat(192),
        ],
    );
    Current {
        frame: app(
            "IRFrame.mk",
            [
                nat(u64::from(FUNCTION.index())),
                nat(u64::from(BLOCK.index())),
                nat(0),
                list("IRBinding", &[app("IRBinding.mk", [nat(0), pair])]),
                list("Nat", &[]),
            ],
        ),
        tail: list("IRFrame", &[]),
        legacy_memory: list("IRMemSlot", &[]),
        legacy_cursor: nat(0),
        world: app(
            "IRByteWorldV1.mk",
            [
                constant("Nat"),
                memory,
                nat(37),
                list("Nat", &[nat(8)]),
                nat(9),
            ],
        ),
    }
}

fn fit(model: &MachineModel, ty: Expr, scalar: Expr) -> Expr {
    app(
        "ir_byte_value_matches_v1",
        [model.context().clone(), ty, scalar],
    )
}

fn truth() -> PendingEquality {
    PendingEquality::reflexive(constant("Bool"), constant("Bool.true"))
}

fn word_fit(model: &MachineModel, signed: bool, word: Expr, bound: Expr) -> PendingEquality {
    let ty = app(if signed { "IRTy.int_" } else { "IRTy.uint_" }, [nat(64)]);
    PendingEquality::candidate(
        constant("Bool"),
        fit(model, ty, app("IRScalar.int_", [word.clone()])),
        constant("Bool.true"),
        app(
            if signed {
                "ir_byte_i64_value_fits_v1"
            } else {
                "ir_byte_u64_value_fits_v1"
            },
            [model.context().clone(), word, bound],
        ),
    )
}

fn pair_fit(
    model: &MachineModel,
    pair: Expr,
    first: PendingEquality,
    second: PendingEquality,
) -> PendingEquality {
    let fields = joined(first, joined(second, truth()));
    PendingEquality::candidate(
        constant("Bool"),
        fit(
            model,
            app("IRTy.struct_", [nat(u64::from(PAIR.index()))]),
            pair,
        ),
        constant("Bool.true"),
        fields.term,
    )
}

#[derive(Clone, Copy, Debug)]
enum Mutation {
    None,
    ConcreteUnselectedLane,
    WholeEvaluatorRefl,
    StaleAggregate,
    StaleUnselectedLane,
    WrongSelected,
    WrongFieldTypes,
    ForgedAggregateAdmission,
    ForgedSelectedAdmission,
    WrongPc,
    WrongWorld,
}

fn proof(mutation: Mutation, full_run: bool) -> (Expr, Expr) {
    let module = fixture();
    let reflected = reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block: BLOCK,
            instruction: 0,
        })
        .unwrap();
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let status = assembler.local(constant("Nat")).unwrap();
    let payload = assembler.local(constant("Nat")).unwrap();
    let bound_type = |word: Expr| {
        eq(
            &constant("Bool"),
            app("ir_nat_ltb", [word, app("ir_nat_pow2", [nat(64)])]),
            constant("Bool.true"),
        )
    };
    let status_bound = assembler.local(bound_type(status.term().clone())).unwrap();
    let payload_bound = assembler.local(bound_type(payload.term().clone())).unwrap();
    let status_scalar = app("IRScalar.int_", [status.term().clone()]);
    let payload_scalar = app("IRScalar.int_", [payload.term().clone()]);
    let concrete_payload = matches!(
        mutation,
        Mutation::ConcreteUnselectedLane | Mutation::StaleUnselectedLane
    );
    let genuine_pair = aggregate(
        status_scalar.clone(),
        if concrete_payload {
            app("IRScalar.int_", [nat(11)])
        } else {
            payload_scalar.clone()
        },
    );
    let before = current(genuine_pair.clone());
    let stale = matches!(mutation, Mutation::StaleAggregate);
    let wrong_value = matches!(mutation, Mutation::WrongSelected);
    let pair = if stale {
        aggregate(payload_scalar.clone(), status_scalar.clone())
    } else if matches!(mutation, Mutation::StaleUnselectedLane) {
        // Both concrete payloads are admitted and ExtractField0 observes the
        // identical symbolic status. Only the whole-SSA provenance differs.
        aggregate(status_scalar.clone(), app("IRScalar.int_", [nat(0)]))
    } else {
        genuine_pair.clone()
    };
    let first_word = if stale { &payload } else { &status };
    let first_bound = if stale { &payload_bound } else { &status_bound };
    let second_word = if stale { &status } else { &payload };
    let second_bound = if stale { &status_bound } else { &payload_bound };
    let mut admitted = pair_fit(
        &model,
        pair.clone(),
        word_fit(
            &model,
            false,
            first_word.term().clone(),
            first_bound.term().clone(),
        ),
        if concrete_payload {
            word_fit(
                &model,
                true,
                nat(if matches!(mutation, Mutation::StaleUnselectedLane) {
                    0
                } else {
                    11
                }),
                truth().term,
            )
        } else {
            word_fit(
                &model,
                true,
                second_word.term().clone(),
                second_bound.term().clone(),
            )
        },
    );
    let selected_value = if wrong_value {
        payload_scalar.clone()
    } else {
        status_scalar.clone()
    };
    let mut selected = word_fit(
        &model,
        false,
        if wrong_value {
            payload.term()
        } else {
            status.term()
        }
        .clone(),
        if wrong_value {
            payload_bound.term()
        } else {
            status_bound.term()
        }
        .clone(),
    );
    if matches!(mutation, Mutation::ForgedAggregateAdmission) {
        admitted.term = truth().term;
    }
    if matches!(mutation, Mutation::ForgedSelectedAdmission) {
        selected.term = truth().term;
    }
    let checks = site
        .scalar_checks(&model, &before, selected_value.clone())
        .unwrap();
    let allocated_before = assembler.local_scope().allocated();
    let evaluated = if matches!(mutation, Mutation::WholeEvaluatorRefl) {
        assembler
            .conversion(
                constant("IRStepResult"),
                checks.evaluation.clone(),
                app("IRStepResult.value", [selected_value.clone()]),
            )
            .unwrap()
    } else {
        let mut field_types = vec![app("IRTy.uint_", [nat(64)]), app("IRTy.int_", [nat(64)])];
        if matches!(mutation, Mutation::WrongFieldTypes) {
            field_types.reverse();
        }
        site.extract_field(
            &mut assembler,
            &model,
            &before,
            selected_value.clone(),
            ExtractFieldPremises {
                aggregate: pair,
                field_types,
                admitted,
                selected: selected.clone(),
            },
        )
        .unwrap()
    };
    assert_eq!(
        assembler.local_scope().allocated(),
        allocated_before,
        "exact SSA lifting must introduce no fresh scoped local"
    );
    let (mut term, mut proposition) = if full_run {
        let operands = assembler
            .conversion(constant("Bool"), checks.operands, constant("Bool.true"))
            .unwrap();
        let result_guard = joined(truth(), joined(selected, truth()));
        let result = PendingEquality::candidate(
            constant("Bool"),
            checks.result,
            constant("Bool.true"),
            result_guard.term,
        );
        let valid = assembler
            .conversion(
                constant("Bool"),
                before.valid(&model),
                constant("Bool.true"),
            )
            .unwrap();
        let transfer = site
            .scalar_value(
                &mut assembler,
                &model,
                &before,
                selected_value,
                ScalarPremises {
                    evaluated,
                    operands,
                    result,
                    before: valid,
                },
            )
            .unwrap();
        // Independent concrete frame spelling: actual destination1 is prepended
        // once; PC advances once, input0 and every other machine/world lane stay.
        let after = Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(u64::from(FUNCTION.index())),
                    nat(u64::from(BLOCK.index())),
                    nat(if matches!(mutation, Mutation::WrongPc) {
                        2
                    } else {
                        1
                    }),
                    list(
                        "IRBinding",
                        &[
                            app("IRBinding.mk", [nat(1), status_scalar.clone()]),
                            app("IRBinding.mk", [nat(0), genuine_pair]),
                        ],
                    ),
                    list("Nat", &[]),
                ],
            ),
            ..before.clone()
        };
        let mut endpoint = after.running(&model);
        if matches!(mutation, Mutation::WrongWorld) {
            let mut altered = after;
            let fields = altered.world.get_app_args();
            let world = app(
                "IRByteWorldV1.mk",
                [
                    fields[0].clone(),
                    fields[1].clone(),
                    nat(38),
                    fields[3].clone(),
                    fields[4].clone(),
                ],
            );
            drop(fields);
            altered.world = world;
            endpoint = altered.running(&model);
        }
        (
            transfer.run().equality().term().clone(),
            eq(
                &model.config_type(),
                model.run(&NatTerm::literal(1), before.running(&model)),
                endpoint,
            ),
        )
    } else {
        // Reconstruct the evaluator from the exact source lane and actual
        // source row, not from evaluated.left or evaluated.right.
        (
            evaluated.term,
            eq(
                &constant("IRStepResult"),
                app(
                    "ir_byte_extract_field_v1",
                    [
                        model.context().clone(),
                        site.site.clone(),
                        app("IRTy.uint_", [nat(64)]),
                        nat(0),
                        app("ir_getd", [before.machine(), nat(0)]),
                        nat(0),
                    ],
                ),
                app("IRStepResult.value", [status_scalar]),
            ),
        )
    };
    drop(assembler);
    for local in [&status, &payload, &status_bound, &payload_bound]
        .into_iter()
        .rev()
    {
        term = local.lam(term);
        proposition = local.pi(proposition);
    }
    (
        scope.close(&term).unwrap(),
        scope.close(&proposition).unwrap(),
    )
}

fn replay(term: &Expr, proposition: &Expr, accepted: bool, label: &str) {
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    assert!(!proposition.has_fvar_quick() && !proposition.has_loose_bvars());
    let checker = checker();
    checker
        .check_type(proposition, &Expr::sort(Level::zero()))
        .unwrap();
    let result = checker.check_type(term, proposition);
    assert!(
        !checker.heartbeat_spent(),
        "{label}: semantic kernel result required"
    );
    if accepted {
        result.unwrap();
        let audit = environment().audit_certification(proposition, term);
        assert!(audit.is_certified(), "{label}: {audit:#?}");
        for dependency in &audit.dependencies {
            assert!(environment().axiom_deps(dependency).unwrap().is_empty());
            assert!(
                environment()
                    .trust_marker_deps(dependency)
                    .unwrap()
                    .is_empty()
            );
        }
        let encoded = trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
        assert_eq!(&decoded, term);
        assert!(
            environment()
                .audit_certification(proposition, &decoded)
                .is_certified()
        );
    } else {
        assert!(
            matches!(result, Err(KernelTypeError::TypeMismatch { .. })),
            "{label}: {result:?}"
        );
    }
}

#[test]
fn symbolic_extract_field_replays_exact_evaluator_and_fetched_one_step() {
    for (mutation, full_run) in [
        (Mutation::None, false),
        (Mutation::None, true),
        (Mutation::ConcreteUnselectedLane, true),
    ] {
        let (term, proposition) = proof(mutation, full_run);
        replay(
            &term,
            &proposition,
            true,
            if full_run {
                "actual fetched run"
            } else {
                "actual nominal evaluator"
            },
        );
    }
}

#[test]
fn symbolic_extract_field_preserves_admission_layout_and_actual_ssa_obligations() {
    for mutation in [
        Mutation::WholeEvaluatorRefl,
        Mutation::StaleAggregate,
        Mutation::StaleUnselectedLane,
        Mutation::WrongSelected,
        Mutation::WrongFieldTypes,
        Mutation::ForgedAggregateAdmission,
        Mutation::ForgedSelectedAdmission,
        Mutation::WrongPc,
        Mutation::WrongWorld,
    ] {
        let (term, proposition) = proof(mutation, true);
        replay(&term, &proposition, false, &format!("{mutation:?}"));
    }
}

#[test]
fn symbolic_extract_field_operand_projection_is_bounded_exact_and_fail_closed() {
    let row = |id, ty| app("IRByteOperandV1.mk", [nat(id), ty]);
    let ty = app("IRTy.struct_", [nat(19)]);
    let other = app("IRTy.uint_", [nat(64)]);
    let rows = list("IRByteOperandV1", &[row(0, ty.clone()), row(1, other)]);
    assert_eq!(aggregate_type(&rows, &nat(0), 2).unwrap(), ty);
    assert_eq!(
        aggregate_type(&rows, &nat(0), 1).err().unwrap(),
        "field extraction operand catalog construction cap"
    );
    let poisoned = app(
        "IRList.cons",
        [
            constant("IRByteOperandV1"),
            row(0, ty.clone()),
            constant("True"),
        ],
    );
    assert_eq!(
        aggregate_type(&poisoned, &nat(0), 1).err().unwrap(),
        "field extraction operand catalog construction cap"
    );
    assert_eq!(
        aggregate_type(&rows, &nat(2), 2).err().unwrap(),
        "field extraction operand catalog lacks actual source"
    );
    let duplicate = list("IRByteOperandV1", &[row(0, ty.clone()), row(0, ty)]);
    assert_eq!(
        aggregate_type(&duplicate, &nat(0), 2).err().unwrap(),
        "field extraction operand catalog repeats actual source"
    );
    for malformed in [
        list("IRTy", &[]),
        list("IRByteOperandV1", &[constant("True")]),
    ] {
        assert!(aggregate_type(&malformed, &nat(0), 2).is_err());
    }
}

#[test]
fn symbolic_extract_field_keeps_typed_source_context_endpoint_and_construction_guards() {
    let module = fixture();
    let reflected = reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let coordinate = Coordinate {
        function: FUNCTION,
        block: BLOCK,
        instruction: 0,
    };
    let genuine = catalog.fetch(coordinate).unwrap();
    let returned = catalog
        .fetch(Coordinate {
            instruction: 1,
            ..coordinate
        })
        .unwrap();
    let scalar = app("IRScalar.int_", [nat(0)]);
    let pair = aggregate(scalar.clone(), scalar.clone());
    let before = current(pair.clone());
    let premises = || {
        let selected = word_fit(&model, false, nat(0), truth().term);
        let payload = word_fit(&model, true, nat(0), truth().term);
        ExtractFieldPremises {
            aggregate: pair.clone(),
            field_types: vec![app("IRTy.uint_", [nat(64)]), app("IRTy.int_", [nat(64)])],
            admitted: pair_fit(&model, pair.clone(), selected.clone(), payload),
            selected,
        }
    };
    let mut foreign_context = genuine.clone();
    foreign_context.context = constant("True");
    let mut old_site = genuine.clone();
    let old_fields: Vec<_> = old_site
        .site
        .get_app_args()
        .into_iter()
        .take(6)
        .cloned()
        .collect();
    old_site.site = app("IRByteSiteV1.mk", old_fields);
    let mut wrong_pc = genuine.clone();
    let mut fields: Vec<_> = wrong_pc.site.get_app_args().into_iter().cloned().collect();
    fields[2] = nat(1);
    wrong_pc.site = app("IRByteSiteV1.mkt", fields);
    let mut absent_source = genuine.clone();
    let mut fields: Vec<_> = absent_source
        .site
        .get_app_args()
        .into_iter()
        .cloned()
        .collect();
    fields[6] = list("IRByteOperandV1", &[]);
    absent_source.site = app("IRByteSiteV1.mkt", fields);
    for (site, expected) in [
        (returned, "field extraction requires actual ExtractField"),
        (
            foreign_context,
            "field extraction context: different candidate terms; supply an explicit equality transport",
        ),
        (
            old_site,
            "field extraction requires actual typed operand catalog",
        ),
        (
            wrong_pc,
            "field extraction site coordinate: different candidate terms; supply an explicit equality transport",
        ),
        (
            absent_source,
            "field extraction operand catalog lacks actual source",
        ),
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let error = site
            .extract_field(&mut assembler, &model, &before, scalar.clone(), premises())
            .err()
            .unwrap();
        assert_eq!(error, expected);
    }
    for too_many_fields in [false, true] {
        let mut supplied = premises();
        if too_many_fields {
            supplied.field_types = vec![constant("IRTy.bool_"); limits().max_list_items + 1];
        } else {
            supplied.admitted.left = constant("Bool.true");
        }
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let error = genuine
            .extract_field(&mut assembler, &model, &before, scalar.clone(), supplied)
            .err()
            .unwrap();
        assert_eq!(
            error,
            if too_many_fields {
                "field extraction nominal field construction cap"
            } else {
                "equality left endpoint: different candidate terms; supply an explicit equality transport"
            }
        );
    }
    let mut policy = limits();
    policy.max_operations = 1;
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    assert_eq!(
        genuine
            .extract_field(&mut assembler, &model, &before, scalar, premises())
            .err()
            .unwrap(),
        "execution construction operation budget exceeded"
    );
    assert_eq!(assembler.operations, policy.max_operations);
    assert_eq!(assembler.local_scope().allocated(), 0);
}

#[test]
fn ranked_site_catalog_proves_original_guard_and_refuses_wrong_catalogs() {
    let module = fixture();
    let reflected = reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let proof = assembler.site_catalog_uniqueness(&model).unwrap().unwrap();
    checker()
        .check_type(proof.term(), &proof.proposition())
        .unwrap();
    let before = assembler.operations();
    let again = assembler.site_catalog_uniqueness(&model).unwrap().unwrap();
    assert_eq!(assembler.operations(), before + 1);
    assert_eq!(again.proposition(), proof.proposition());
    assert_eq!(again.term(), proof.term());

    let fields = model.context().get_app_args();
    let mut cursor = fields[4].clone();
    let mut sites = Vec::new();
    while cursor.get_app_fn() == &constant("IRList.cons") {
        let row = cursor.get_app_args();
        sites.push(row[1].clone());
        let next = row[2].clone();
        drop(row);
        cursor = next;
    }
    assert_eq!(
        sites.len(),
        2,
        "the real field fixture has ExtractField and Return"
    );
    let changed = |items: Vec<Expr>| {
        let mut fields: Vec<_> = fields.iter().map(|field| (*field).clone()).collect();
        fields[4] = list("IRByteSiteV1", &items);
        MachineModel {
            context: app("IRByteContextV1.mk", fields),
            ..model.clone()
        }
    };
    let mut reversed = sites.clone();
    reversed.reverse();
    for wrong in [
        changed(vec![sites[0].clone(), sites[0].clone()]),
        changed(vec![sites[0].clone(), sites[1].clone(), sites[0].clone()]),
        changed(reversed),
    ] {
        assert!(assembler.site_catalog_uniqueness(&wrong).unwrap().is_none());
        let goal = eq(
            &constant("Bool"),
            app(
                "ir_byte_sites_unique_v1",
                [app("ir_byte_context_sites_v1", [wrong.context().clone()])],
            ),
            constant("Bool.true"),
        );
        let mut arguments: Vec<_> = proof
            .term()
            .get_app_args()
            .iter()
            .map(|term| (*term).clone())
            .collect();
        arguments[2] = wrong.context().get_app_args()[4].clone();
        let transplanted_chain = Expr::apps(proof.term().get_app_fn().clone(), arguments);
        assert!(matches!(
            checker().check_type(&transplanted_chain, &goal),
            Err(KernelTypeError::TypeMismatch { .. })
        ));
    }
    // Selection arithmetic is fallible. An overflowing rank must retain the
    // existing general proof route instead of wrapping into a certificate.
    let mut huge_fields: Vec<_> = sites[0]
        .get_app_args()
        .iter()
        .map(|field| (*field).clone())
        .collect();
    huge_fields[0] = nat(u64::MAX);
    let overflowing = changed(vec![Expr::apps(sites[0].get_app_fn().clone(), huge_fields)]);
    assert!(
        assembler
            .site_catalog_uniqueness(&overflowing)
            .unwrap()
            .is_none()
    );

    // Unordered does not mean nonunique. The old route remains valid for a
    // genuinely unique reversed catalog; only transplanting its chain is false.
    let mut reversed = sites.clone();
    reversed.reverse();
    let unordered = changed(reversed);
    let original_goal = eq(
        &constant("Bool"),
        app(
            "ir_byte_sites_unique_v1",
            [app(
                "ir_byte_context_sites_v1",
                [unordered.context().clone()],
            )],
        ),
        constant("Bool.true"),
    );
    checker()
        .check_type(
            &refl(&constant("Bool"), constant("Bool.true")),
            &original_goal,
        )
        .unwrap();
    let mut tiny_scope = Scope::new();
    let mut tiny = Assembler::new(
        &mut tiny_scope,
        Limits {
            max_operations: 2,
            ..limits()
        },
    )
    .unwrap();
    assert!(tiny.site_catalog_uniqueness(&model).is_err());
    assert!(tiny.site_catalog_uniqueness(&model).is_err());
}

#[test]
fn ranked_original_673_site_catalog_retains_full_guard_with_bounded_replay() {
    let module: Module = serde_json::from_str(include_str!(
        "../tests/fixtures/source-enabled-native-module.json"
    ))
    .unwrap();
    assert!(crate::validate_module(&module).is_empty());
    assert_eq!(
        module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .map(|b| b.body.len())
            .sum::<usize>(),
        673
    );
    let addresses: Vec<_> = module
        .functions
        .iter()
        .enumerate()
        .map(|(index, function)| (function.id, 4096 + 64 * index as u64))
        .collect();
    let reflected = reflect_core_module_v1(&module, &addresses).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(
        &mut scope,
        Limits {
            max_operations: 10_000,
            ..limits()
        },
    )
    .unwrap();
    let construction_started = std::time::Instant::now();
    let candidate = assembler.site_catalog_uniqueness(&model).unwrap().unwrap();
    let construction_elapsed = construction_started.elapsed();
    let mut reference = checker();
    reference.set_heartbeat_limit(2_000_000);
    reference.enable_heartbeat_profiler();
    let original_refl = refl(&constant("Bool"), constant("Bool.true"));
    reference
        .check_type(&original_refl, &candidate.proposition())
        .unwrap();
    let original_work = reference.heartbeat_profile().unwrap().total();
    let mut optimized = checker();
    optimized.set_heartbeat_limit(2_000_000);
    optimized.enable_heartbeat_profiler();
    optimized
        .check_type(candidate.term(), &candidate.proposition())
        .unwrap();
    let ranked_work = optimized.heartbeat_profile().unwrap().total();
    eprintln!(
        "ORIGINAL_673_SITE_CATALOG original_guard_refl={original_work} same_guard_ranked={ranked_work} construction={} construction_elapsed={construction_elapsed:?} original_proof_bytes={} ranked_proof_bytes={} unchanged_claim_bytes={}",
        assembler.operations(),
        trust_ir::proof::encode_clean_expr_dag_v2(&original_refl)
            .unwrap()
            .len(),
        trust_ir::proof::encode_clean_expr_dag_v2(candidate.term())
            .unwrap()
            .len(),
        trust_ir::proof::encode_clean_expr_dag_v2(&candidate.proposition())
            .unwrap()
            .len(),
    );
    assert!(
        ranked_work < original_work,
        "original guard must do less kernel work"
    );
    let audit = environment().audit_certification(&candidate.proposition(), candidate.term());
    assert!(audit.is_certified(), "{audit:?}");
}

#[test]
fn neutral_site_valid_transport_keeps_complete_guards_and_rejects_wrong_catalog_or_result() {
    let law = super::super::field_site_valid::closed_candidate();
    let claim = super::super::field_site_valid::closed_claim();
    assert!(!law.has_fvar_quick() && !law.has_loose_bvars());
    checker().check_type(&law, &claim).unwrap();
    let wire = trust_ir::proof::encode_clean_expr_dag_v2(&law).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&wire).unwrap();
    checker().check_type(&decoded, &claim).unwrap();
    assert!(
        environment()
            .audit_certification(&claim, &decoded)
            .is_certified()
    );
    let module = fixture();
    let reflected = reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let context_fields = model.context().get_app_args();
    let sites = context_fields[4].get_app_args();
    let site = sites[1].clone();
    let site_fields = site.get_app_args();
    let rows = site_fields[6].clone();
    let ty = app("IRTy.uint_", [nat(64)]);
    let apply = |ctx: Expr, result_ty: Expr, proof: Expr| {
        Expr::apps(
            law.clone(),
            [ctx, site.clone(), rows.clone(), result_ty, proof],
        )
    };
    let goal = |ctx: Expr, result_ty: Expr| {
        eq(
            &constant("Bool"),
            app(
                "ir_byte_field_site_valid_v1",
                [ctx, site.clone(), rows.clone(), result_ty],
            ),
            constant("Bool.true"),
        )
    };
    let original = apply(
        model.context().clone(),
        ty.clone(),
        refl(&constant("Bool"), constant("Bool.true")),
    );
    checker()
        .check_type(&original, &goal(model.context().clone(), ty.clone()))
        .unwrap();
    let mut changed: Vec<_> = context_fields.iter().map(|e| (*e).clone()).collect();
    changed[4] = list("IRByteSiteV1", &[site.clone(), site.clone()]);
    let duplicated = app("IRByteContextV1.mk", changed);
    for (ctx, result_ty, proof) in [
        (
            duplicated,
            ty.clone(),
            refl(&constant("Bool"), constant("Bool.true")),
        ),
        (
            model.context().clone(),
            constant("IRTy.bool_"),
            refl(&constant("Bool"), constant("Bool.true")),
        ),
        (model.context().clone(), ty, constant("True.intro")),
    ] {
        assert!(matches!(
            checker().check_type(
                &apply(ctx.clone(), result_ty.clone(), proof),
                &goal(ctx, result_ty)
            ),
            Err(KernelTypeError::TypeMismatch { .. })
        ));
    }
}
