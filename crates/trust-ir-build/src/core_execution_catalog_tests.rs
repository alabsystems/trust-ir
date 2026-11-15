// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual reflected-block/site constituent reuse, with the original fetched kernel
//! equations. Structural projection is candidate discovery, never a proof of
//! source execution or a license to trust a cached/forged node.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{
    Endianness, FieldDef, Module, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo,
    Ty,
};

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

fn fixture(literal_offset: u64, constants: usize) -> (Module, Vec<Coordinate>) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "catalog_constituents",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![], vec![Ty::U64]);
    let functions = [
        builder.declare_function("first", signature),
        builder.declare_function("second", signature),
    ];
    let mut coordinates = Vec::new();
    for (function_index, function) in functions.into_iter().enumerate() {
        let mut body = builder.define_function(function).unwrap();
        let blocks = [body.create_block(), body.create_block()];
        for (block_index, block) in blocks.into_iter().enumerate() {
            body.switch_to_block(block);
            let mut returned = None;
            for instruction in 0..constants {
                returned = Some(body.uconst(
                    Ty::U64,
                    u128::from(
                        literal_offset
                            + 11
                            + 100 * function_index as u64
                            + 10 * block_index as u64
                            + instruction as u64,
                    ),
                ));
                coordinates.push(Coordinate {
                    function,
                    block,
                    instruction,
                });
            }
            if block_index == 0 {
                body.br(blocks[1], vec![]);
            } else {
                body.ret(vec![returned.expect("fixture has constants")]);
            }
            coordinates.push(Coordinate {
                function,
                block,
                instruction: constants,
            });
        }
        body.build();
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let validation = crate::validate_module(&module);
    assert!(validation.is_empty(), "{validation:?}");
    (module, coordinates)
}

fn addresses(module: &Module) -> Vec<(FuncId, u64)> {
    module
        .functions
        .iter()
        .map(|function| (function.id, 4096 * (u64::from(function.id.index()) + 1)))
        .collect()
}

fn legacy_node(block: &Expr, pc: usize) -> Expr {
    let lookup = app(
        "ir_nodes_get",
        [app("ir_block_nodes", [block.clone()]), nat(pc as u64)],
    );
    let checker = checker();
    checker
        .check_type(&lookup, &app("IROption", [constant("IRNode")]))
        .unwrap();
    let reduced = checker.whnf(&lookup);
    assert!(!checker.heartbeat_spent());
    assert_eq!(reduced.get_app_fn(), &constant("IROption.some"));
    (*reduced.get_app_args()[1]).clone()
}

fn legacy_site(context: &Expr, coordinate: Coordinate) -> Expr {
    let lookup = app(
        "ir_byte_site_v1",
        [
            context.clone(),
            nat(u64::from(coordinate.function.index())),
            nat(u64::from(coordinate.block.index())),
            nat(coordinate.instruction as u64),
        ],
    );
    let checker = checker();
    checker
        .check_type(&lookup, &app("IROption", [constant("IRByteSiteV1")]))
        .unwrap();
    let reduced = checker.whnf(&lookup);
    assert!(!checker.heartbeat_spent());
    assert_eq!(reduced.get_app_fn(), &constant("IROption.some"));
    (*reduced.get_app_args()[1]).clone()
}

#[test]
fn catalog_node_projection_is_exact_legacy_lookup_under_nominal_source_permutations() {
    let (original, coordinates) = fixture(0, 2);
    for reversed in [false, true] {
        let mut module = original.clone();
        if reversed {
            module.functions.reverse();
            for function in &mut module.functions {
                function.blocks.reverse();
            }
        }
        assert!(crate::validate_module(&module).is_empty());
        let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        // Reverse PCs as well: there is no retained forward-only cursor or
        // vector-position interpretation that could silently change the node.
        for coordinate in coordinates.iter().rev() {
            let site = catalog.fetch(*coordinate).unwrap();
            assert_eq!(site.coordinate(), *coordinate);
            assert_eq!(site.node, legacy_node(&site.block, coordinate.instruction));
            assert_eq!(
                site.site,
                legacy_site(reflected.context_term(), *coordinate)
            );
            let fields = site.node.get_app_args();
            assert_eq!(*fields[0], site.instruction);
            assert_eq!(*fields[1], site.results);
        }
        assert_eq!(catalog.functions.len(), 2);
        assert_eq!(catalog.blocks.len(), 4);
        assert!(
            catalog.sites.is_empty(),
            "no retained per-PC metadata index"
        );
        assert_eq!(
            catalog.lookups,
            2 + 4,
            "only genuine function/block reductions"
        );
        assert!(catalog.calls.is_empty());
    }
}

#[test]
fn catalog_projection_reuses_typed_container_without_charging_another_discovery() {
    let (module, coordinates) = fixture(0, 2);
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let mut policy = limits();
    policy.max_lookup_candidates = 4;
    let mut catalog = Catalog::new(environment(), &reflected, policy).unwrap();
    let first = catalog.fetch(coordinates[0]).unwrap();
    assert_eq!(catalog.lookups, 2, "actual function and block reductions");
    let before = catalog.lookups;
    for coordinate in &coordinates[..3] {
        assert_eq!(
            catalog.block_node(*coordinate, &first.block).unwrap(),
            legacy_node(&first.block, coordinate.instruction)
        );
    }
    assert_eq!(catalog.lookups, before, "no new lookup was performed");
    assert!(
        catalog.sites.is_empty(),
        "canonical sites are shared on demand"
    );
    assert_eq!(catalog.fetch(coordinates[0]).unwrap().node, first.node);
    assert_eq!(catalog.lookups, 2, "same typed containers are cached");
    for coordinate in &coordinates[..3] {
        catalog.fetch(*coordinate).unwrap();
    }
    assert_eq!(
        catalog.lookups, 2,
        "new PCs require no new kernel reductions"
    );
    catalog.call_target(coordinates[0].function).unwrap();
    assert_eq!(catalog.lookups, policy.max_lookup_candidates);
    assert_eq!(
        catalog.fetch(coordinates[6]).err().unwrap(),
        "reflected lookup candidate budget exceeded"
    );
    assert_eq!(catalog.lookups, policy.max_lookup_candidates);
    assert!(
        catalog.sites.is_empty(),
        "no canonical or refused PC entries"
    );
    assert_eq!(catalog.functions.len(), 1);
    assert_eq!(catalog.blocks.len(), 1);
    // Typed container/call hits remain usable at the exact unchanged cap. A
    // genuinely new function or binding still fails before kernel reduction.
    catalog.fetch(coordinates[0]).unwrap();
    catalog.call_target(coordinates[0].function).unwrap();
    assert_eq!(
        catalog.call_target(coordinates[6].function).err().unwrap(),
        "reflected lookup candidate budget exceeded"
    );
    assert_eq!(catalog.calls.len(), 1);
    assert_eq!(catalog.lookups, policy.max_lookup_candidates);

    // A different block plus the binding uses the same four discoveries. The
    // next, genuinely necessary signature reduction must still refuse.
    let mut signature_bounded = Catalog::new(environment(), &reflected, policy).unwrap();
    signature_bounded.fetch(coordinates[0]).unwrap();
    signature_bounded.fetch(coordinates[3]).unwrap();
    assert_eq!(signature_bounded.lookups, 3);
    assert_eq!(
        signature_bounded
            .call_target(coordinates[0].function)
            .err()
            .unwrap(),
        "reflected lookup candidate budget exceeded"
    );
    assert_eq!(signature_bounded.lookups, 4);
    assert!(
        signature_bounded.calls.is_empty(),
        "partial binding/signature is not retained"
    );
    signature_bounded.fetch(coordinates[1]).unwrap();
    signature_bounded.fetch(coordinates[4]).unwrap();
    assert_eq!(signature_bounded.lookups, 4);
    assert_eq!(signature_bounded.blocks.len(), 2);
}

fn block_with_nodes(id: BlockId, nodes: Expr) -> Expr {
    app(
        "IRBlock.mk",
        [nat(u64::from(id.index())), list("Nat", &[]), nodes],
    )
}

fn context_with_sites(context: &Expr, sites: Expr) -> Expr {
    let fields = exact_constructor_fields::<5>(context, "IRByteContextV1.mk").unwrap();
    app(
        "IRByteContextV1.mk",
        [
            (*fields[0]).clone(),
            (*fields[1]).clone(),
            (*fields[2]).clone(),
            (*fields[3]).clone(),
            sites,
        ],
    )
}

fn site_at(coordinate: Coordinate, typed: bool, align: u64, convention: u64) -> Expr {
    let mut fields = vec![
        nat(u64::from(coordinate.function.index())),
        nat(u64::from(coordinate.block.index())),
        nat(coordinate.instruction as u64),
        nat(align),
        nat(convention),
        list("IRTy", &[app("IRTy.uint_", [nat(64)])]),
    ];
    if typed {
        fields.push(list(
            "IRByteOperandV1",
            &[app("IRByteOperandV1.mk", [nat(601), constant("IRTy.ptr_")])],
        ));
    }
    app(
        if typed {
            "IRByteSiteV1.mkt"
        } else {
            "IRByteSiteV1.mk"
        },
        fields,
    )
}

fn same_constituent(actual: &Expr, expected: &Expr) {
    assert_eq!(actual, expected);
    let (ExprKind::App(actual_head, actual_last), ExprKind::App(expected_head, expected_last)) =
        (actual.kind(), expected.kind())
    else {
        panic!("site constructor application required");
    };
    assert!(std::sync::Arc::ptr_eq(actual_head, expected_head));
    assert!(std::sync::Arc::ptr_eq(actual_last, expected_last));
}

#[test]
fn site_projection_is_head_first_and_keeps_exact_old_and_typed_payloads() {
    let (module, coordinates) = fixture(0, 2);
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let coordinate = coordinates[0];
    let unrelated = site_at(coordinates[6], false, 2, 3);
    let old = site_at(coordinate, false, 8, 1);
    let typed = site_at(coordinate, true, 16, 4);
    for entries in [
        vec![unrelated.clone(), old.clone(), typed.clone()],
        vec![typed.clone(), old.clone(), unrelated.clone()],
    ] {
        let context = context_with_sites(reflected.context_term(), list("IRByteSiteV1", &entries));
        let projected = catalog
            .projected_byte_site(coordinate, &context)
            .unwrap()
            .unwrap();
        let expected = if entries[0] == unrelated {
            &old
        } else {
            &typed
        };
        same_constituent(&projected, expected);
        assert_eq!(
            projected,
            legacy_site(&context, coordinate),
            "first head, not last duplicate"
        );
        assert_eq!(
            catalog.lookups, 0,
            "projection does not spend a kernel discovery"
        );
        assert!(catalog.sites.is_empty(), "no per-node metadata index");
    }
}

#[test]
fn site_projection_preserves_traversal_bound_and_shape_refusals() {
    let (module, coordinates) = fixture(0, 2);
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let coordinate = coordinates[0];
    let matching = site_at(coordinate, true, 8, 2);
    let mut policy = limits();
    policy.lookup_heartbeats = 1;
    let bounded = Catalog::new(environment(), &reflected, policy).unwrap();
    let first_then_malformed = context_with_sites(
        reflected.context_term(),
        app(
            "IRList.cons",
            [constant("IRByteSiteV1"), matching.clone(), constant("True")],
        ),
    );
    same_constituent(
        &bounded
            .projected_byte_site(coordinate, &first_then_malformed)
            .unwrap()
            .unwrap(),
        &matching,
    );
    assert_eq!(
        bounded
            .projected_byte_site(coordinates[1], &first_then_malformed)
            .err()
            .unwrap(),
        "actual IRByteSiteV1 projection exhausted its traversal budget",
        "refuse before touching the unneeded malformed tail"
    );
    let second_then_malformed = context_with_sites(
        reflected.context_term(),
        app(
            "IRList.cons",
            [
                constant("IRByteSiteV1"),
                site_at(coordinates[1], false, 0, 0),
                app(
                    "IRList.cons",
                    [constant("IRByteSiteV1"), matching.clone(), constant("True")],
                ),
            ],
        ),
    );
    assert_eq!(
        bounded
            .projected_byte_site(coordinate, &second_then_malformed)
            .err()
            .unwrap(),
        "actual IRByteSiteV1 projection exhausted its traversal budget"
    );
    policy.lookup_heartbeats = 2;
    let exactly_two = Catalog::new(environment(), &reflected, policy).unwrap();
    same_constituent(
        &exactly_two
            .projected_byte_site(coordinate, &second_then_malformed)
            .unwrap()
            .unwrap(),
        &matching,
    );
    let catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    for sites in [
        list("IRByteSiteV1", &[]),
        list("IRByteSiteV1", &[site_at(coordinates[1], false, 0, 0)]),
    ] {
        let context = context_with_sites(reflected.context_term(), sites);
        assert_eq!(
            catalog
                .projected_byte_site(coordinate, &context)
                .err()
                .unwrap(),
            "actual IRByteSiteV1 projection coordinate absent"
        );
    }
    for sites in [
        constant("True"),
        list("Nat", &[nat(0)]),
        app("IRList.cons", [constant("IRByteSiteV1"), matching.clone()]),
        Expr::apps(
            Expr::const_(Name::from_string("IRList.cons"), vec![Level::zero()]),
            [
                constant("IRByteSiteV1"),
                matching.clone(),
                list("IRByteSiteV1", &[]),
            ],
        ),
        list("IRByteSiteV1", &[constant("opaque_site")]),
        list("IRByteSiteV1", &[app("IRByteSiteV1.mk", [nat(0)])]),
        list("IRByteSiteV1", &[Expr::app(matching.clone(), nat(0))]),
    ] {
        let context = context_with_sites(reflected.context_term(), sites);
        assert!(catalog.projected_byte_site(coordinate, &context).is_err());
    }
    let mut fields = matching
        .get_app_args()
        .iter()
        .map(|field| (*field).clone())
        .collect::<Vec<_>>();
    fields[0] = constant("Nat.zero");
    let nonliteral = app("IRByteSiteV1.mkt", fields.clone());
    let context = context_with_sites(
        reflected.context_term(),
        list("IRByteSiteV1", &[nonliteral]),
    );
    assert_eq!(
        catalog
            .projected_byte_site(coordinate, &context)
            .err()
            .unwrap(),
        "actual IRByteSiteV1 projection requires literal nominal coordinates"
    );
    fields[0] = nat(u64::from(coordinate.function.index()));
    let wrong_levels = Expr::apps(
        Expr::const_(Name::from_string("IRByteSiteV1.mkt"), vec![Level::zero()]),
        fields,
    );
    let context = context_with_sites(
        reflected.context_term(),
        list("IRByteSiteV1", &[wrong_levels]),
    );
    assert!(catalog.projected_byte_site(coordinate, &context).is_err());
    assert_eq!(catalog.lookups, 0);
    assert!(catalog.sites.is_empty());
}

#[test]
fn noncanonical_contexts_do_not_gain_a_projection_typing_verdict() {
    let (module, coordinates) = fixture(0, 2);
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let fields =
        exact_constructor_fields::<5>(reflected.context_term(), "IRByteContextV1.mk").unwrap();
    for malformed in [
        constant("unknown_context"),
        app("IRByteContextV1.mk", [fields[0].clone()]),
        Expr::app(reflected.context_term().clone(), nat(0)),
        Expr::apps(
            Expr::const_(Name::from_string("IRByteContextV1.mk"), vec![Level::zero()]),
            fields.into_iter().cloned(),
        ),
    ] {
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        assert!(
            catalog
                .projected_byte_site(coordinates[0], &malformed)
                .unwrap()
                .is_none()
        );
        assert_eq!(
            catalog.byte_site(coordinates[0], &malformed).err().unwrap(),
            "actual IRByteSiteV1 lookup type check failed; candidate refused"
        );
        assert_eq!(
            catalog.lookups, 1,
            "necessary attempted kernel reduction is charged"
        );
        assert!(catalog.sites.is_empty());
    }
}

#[test]
fn opaque_site_context_retains_real_discovery_and_cached_hits_at_cap() {
    let (module, coordinates) = fixture(0, 2);
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let opaque = Expr::let_named(
        Name::from_string("actual_context_alias"),
        constant("IRByteContextV1"),
        reflected.context_term().clone(),
        Expr::bvar(0),
        false,
    );
    let mut policy = limits();
    policy.max_lookup_candidates = 4;
    let mut catalog = Catalog::new(environment(), &reflected, policy).unwrap();
    assert!(
        catalog
            .projected_byte_site(coordinates[0], &opaque)
            .unwrap()
            .is_none()
    );
    for coordinate in &coordinates[..4] {
        let (site, projected) = catalog.byte_site(*coordinate, &opaque).unwrap();
        assert!(!projected);
        assert_eq!(site, legacy_site(reflected.context_term(), *coordinate));
    }
    assert_eq!(
        catalog.lookups, 4,
        "each necessary opaque lookup is charged"
    );
    assert_eq!(
        catalog.byte_site(coordinates[4], &opaque).err().unwrap(),
        "reflected lookup candidate budget exceeded"
    );
    assert_eq!(catalog.lookups, 4);
    let mut genuine = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(coordinates[0])
        .unwrap();
    genuine.context = opaque.clone();
    // Simulate the private fallback cache's completed fetched candidate, not a
    // public insertion API. A cached hit remains available at the actual cap.
    catalog.sites.insert(coordinates[0], genuine.clone());
    let cached = catalog.fetch(coordinates[0]).unwrap();
    assert_eq!(cached.site, genuine.site);
    assert_eq!(catalog.lookups, 4);
    let mut model = MachineModel::new(constant("Nat"), &reflected, providers());
    model.context = opaque;
    check_step(
        &step(&cached, &model, &current(coordinates[0])),
        true,
        "actual opaque-context fetched equation",
    );
}

#[test]
fn actual_typed_field_site_preserves_legacy_lookup_and_rejects_catalog_forgery() {
    let mut builder = ModuleBuilder::new_with_target_info(
        "actual_typed_site",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let pair = builder.add_struct(StructDef {
        id: StructId::new(0),
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
    let signature = builder.add_func_type(vec![Ty::Struct(pair)], vec![Ty::U64]);
    let function = builder.declare_function("typed_field", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let aggregate = body.add_block_param(block, Ty::Struct(pair));
    body.switch_to_block(block);
    let field = body.extract_field(Ty::U64, aggregate, 0);
    body.ret(vec![field]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let validation = crate::validate_module(&module);
    assert!(validation.is_empty(), "{validation:?}");
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let coordinate = Coordinate {
        function,
        block,
        instruction: 0,
    };
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let genuine = catalog.fetch(coordinate).unwrap();
    let fields = exact_constructor_fields::<7>(&genuine.site, "IRByteSiteV1.mkt").unwrap();
    assert_eq!(
        genuine.site,
        legacy_site(reflected.context_term(), coordinate)
    );
    assert_eq!(catalog.lookups, 2);
    assert!(catalog.sites.is_empty());
    // This is the fetched-step lookup equation, not an assertion that the
    // aggregate operand is safe/present. The field adapter's distinct checks
    // must still establish actual operand catalog AND runtime value premises.
    let before = current(coordinate);
    check_step(
        &step(&genuine, &model, &before),
        true,
        "actual typed field metadata",
    );
    let [_, operand, _] = exact_constructor_fields::<3>(fields[6], "IRList.cons").unwrap();
    let [operand_id, _] = exact_constructor_fields::<2>(operand, "IRByteOperandV1.mk").unwrap();
    let mut forged_fields = fields.into_iter().cloned().collect::<Vec<_>>();
    forged_fields[6] = list(
        "IRByteOperandV1",
        &[app(
            "IRByteOperandV1.mk",
            [operand_id.clone(), constant("IRTy.bool_")],
        )],
    );
    let mut forged = genuine.clone();
    forged.site = app("IRByteSiteV1.mkt", forged_fields);
    check_step(
        &step(&forged, &model, &before),
        false,
        "forged actual typed operand catalog",
    );
    let mut erased = genuine.clone();
    erased.site = app(
        "IRByteSiteV1.mk",
        fields[..6].iter().map(|field| (*field).clone()),
    );
    check_step(
        &step(&erased, &model, &before),
        false,
        "erased typed operand catalog",
    );
    for (index, changed) in [
        (3, nat(16)),
        (4, nat(17)),
        (5, list("IRTy", &[constant("IRTy.bool_")])),
    ] {
        let mut changed_fields = fields.into_iter().cloned().collect::<Vec<_>>();
        changed_fields[index] = changed;
        let mut forged = genuine.clone();
        forged.site = app("IRByteSiteV1.mkt", changed_fields);
        check_step(
            &step(&forged, &model, &before),
            false,
            "changed alignment/convention/result lane",
        );
    }
}

#[test]
fn catalog_projection_charges_before_each_cons_and_refuses_absence_and_wrong_shapes() {
    let (module, coordinates) = fixture(0, 2);
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let fetched = catalog.fetch(coordinates[0]).unwrap();
    let mut policy = limits();
    policy.lookup_heartbeats = 1;
    let bounded = Catalog::new(environment(), &reflected, policy).unwrap();
    let malformed_tail = block_with_nodes(
        coordinates[0].block,
        app(
            "IRList.cons",
            [constant("IRNode"), fetched.node.clone(), constant("True")],
        ),
    );
    assert_eq!(
        bounded.block_node(coordinates[0], &malformed_tail).unwrap(),
        fetched.node
    );
    assert_eq!(
        bounded
            .block_node(coordinates[1], &malformed_tail)
            .err()
            .unwrap(),
        "actual IRNode projection exhausted its traversal budget",
        "budget must refuse before touching the deliberately malformed tail"
    );
    for instruction in [3, usize::MAX] {
        let absent = Coordinate {
            instruction,
            ..coordinates[0]
        };
        assert_eq!(
            catalog.block_node(absent, &malformed_tail).err().unwrap(),
            "actual IRNode projection coordinate absent"
        );
    }
    let absent_block = Coordinate {
        block: BlockId::new(u32::MAX),
        ..coordinates[0]
    };
    assert_eq!(
        catalog
            .block_node(absent_block, &malformed_tail)
            .err()
            .unwrap(),
        "actual IRNode projection block absent"
    );
    let absent_function = Coordinate {
        function: FuncId::new(u32::MAX),
        ..coordinates[0]
    };
    assert_eq!(
        catalog
            .block_node(absent_function, &malformed_tail)
            .err()
            .unwrap(),
        "actual IRNode projection block absent"
    );
    for (block, expected) in [
        (
            constant("True"),
            "actual IRNode projection requires canonical IRBlock.mk",
        ),
        (
            block_with_nodes(BlockId::new(u32::MAX), list("IRNode", &[])),
            "actual IRNode projection nominal block: different candidate terms; supply an explicit equality transport",
        ),
        (
            block_with_nodes(coordinates[0].block, list("IRNode", &[])),
            "actual IRNode projection requires canonical IRList.cons",
        ),
        (
            block_with_nodes(coordinates[0].block, list("Nat", &[nat(0)])),
            "actual IRNode list type: different candidate terms; supply an explicit equality transport",
        ),
    ] {
        assert_eq!(
            catalog.block_node(coordinates[0], &block).err().unwrap(),
            expected
        );
    }
}

#[test]
fn catalog_projection_keeps_actual_node_constructor_and_arity_refusals() {
    let (module, coordinates) = fixture(0, 2);
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    for (node, expected) in [
        (constant("True"), "actual node candidate is not IRNode.mk"),
        (
            app("IRNode.mk", [constant("True")]),
            "actual node candidate has wrong constructor arity",
        ),
    ] {
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        // Deliberately poison the private container cache. An external caller
        // cannot install this untyped block; the actual fetch boundary must
        // nevertheless retain its node-shape refusals, not guess a node.
        catalog.blocks.insert(
            (coordinates[0].function, coordinates[0].block),
            block_with_nodes(coordinates[0].block, list("IRNode", &[node])),
        );
        assert_eq!(catalog.fetch(coordinates[0]).err().unwrap(), expected);
        assert_eq!(
            catalog.lookups, 1,
            "only the genuine function was discovered"
        );
        assert!(catalog.sites.is_empty());
    }
}

fn providers() -> Expr {
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

fn current(coordinate: Coordinate) -> Current {
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
                nat(u64::from(coordinate.function.index())),
                nat(u64::from(coordinate.block.index())),
                nat(coordinate.instruction as u64),
                list("IRBinding", &[]),
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

fn step(site: &FetchedSite, model: &MachineModel, current: &Current) -> PendingEquality {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let valid = assembler
        .conversion(
            constant("Bool"),
            current.valid(model),
            constant("Bool.true"),
        )
        .unwrap();
    let mut step = site.step(&mut assembler, model, current, valid).unwrap();
    drop(assembler);
    step.term = scope.close(&step.term).unwrap();
    step
}

fn check_step(step: &PendingEquality, certified: bool, label: &str) {
    let proposition = step.proposition();
    assert!(!step.term().has_fvar_quick() && !step.term().has_loose_bvars());
    let checker = checker();
    checker
        .check_type(&proposition, &Expr::sort(Level::zero()))
        .unwrap();
    let result = checker.check_type(step.term(), &proposition);
    assert!(
        !checker.heartbeat_spent(),
        "{label}: semantic rejection required"
    );
    if certified {
        result.unwrap();
        let audit = environment().audit_certification(&proposition, step.term());
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
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(step.term()).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        assert_eq!(&decoded, step.term());
        assert!(
            environment()
                .audit_certification(&proposition, &decoded)
                .is_certified()
        );
    } else {
        assert!(
            matches!(result, Err(KernelTypeError::TypeMismatch { .. })),
            "{label}: {result:?}"
        );
        assert!(
            !environment()
                .audit_certification(&proposition, step.term())
                .is_certified()
        );
    }
}

#[test]
fn catalog_projected_nodes_keep_independent_fetched_kernel_obligations() {
    let (module, coordinates) = fixture(0, 2);
    let reflected = reflect_core_module_v1(&module, &addresses(&module)).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let genuine = catalog.fetch(coordinates[0]).unwrap();
    let before = current(coordinates[0]);
    let mut legacy = genuine.clone();
    legacy.node = legacy_node(&legacy.block, coordinates[0].instruction);
    let legacy_fields = legacy.node.get_app_args();
    legacy.instruction = (*legacy_fields[0]).clone();
    legacy.results = (*legacy_fields[1]).clone();
    legacy.site = legacy_site(reflected.context_term(), coordinates[0]);
    assert_eq!(
        step(&genuine, &model, &before).term(),
        step(&legacy, &model, &before).term(),
        "candidate discovery does not change either fetched equation or proof syntax"
    );
    check_step(
        &step(&genuine, &model, &before),
        true,
        "genuine constituent",
    );
    let next = catalog.fetch(coordinates[1]).unwrap();
    let other_block = catalog.fetch(coordinates[3]).unwrap();
    let other_function = catalog.fetch(coordinates[6]).unwrap();
    let mut foreign_node = genuine.clone();
    foreign_node.node = next.node.clone();
    foreign_node.instruction = next.instruction.clone();
    foreign_node.results = next.results.clone();
    let mut foreign_site = genuine.clone();
    foreign_site.site = next.site.clone();
    let mut foreign_block = genuine.clone();
    foreign_block.block = other_block.block;
    let mut foreign_function = genuine.clone();
    foreign_function.function = other_function.function;
    for (label, site, before) in [
        ("foreign actual node", foreign_node, before.clone()),
        ("foreign actual byte site", foreign_site, before.clone()),
        ("foreign actual block", foreign_block, before.clone()),
        ("foreign actual function", foreign_function, before.clone()),
        (
            "wrong real frame PC",
            genuine.clone(),
            current(coordinates[1]),
        ),
    ] {
        check_step(&step(&site, &model, &before), false, label);
    }
    let (changed, _) = fixture(500, 2);
    let changed_reflected = reflect_core_module_v1(&changed, &addresses(&changed)).unwrap();
    let changed_model = MachineModel::new(constant("Nat"), &changed_reflected, providers());
    let mut old_node_in_new_source = genuine;
    old_node_in_new_source.context = changed_reflected.context_term().clone();
    check_step(
        &step(&old_node_in_new_source, &changed_model, &before),
        false,
        "old node paired with another genuine source context",
    );
}
