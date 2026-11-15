// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole canonical execution of typed pointer transport and declared layouts.
//! Pointer carriers do not establish Rust reference validity or memory access.

use super::*;
use trust_ir::{CastOp, TupleLayoutDescriptor};

#[derive(Clone)]
struct PointerSource {
    function: FuncId,
    ty: Ty,
    address: u64,
    other: u64,
    advance: u64,
    store: bool,
}

struct PointerModel;

fn pointer(value: u64) -> Expr {
    app("IRScalar.ptr_", [nat(value)])
}

fn expected_world(source: &PointerSource) -> Expr {
    if !source.store {
        return world(173, 37, &[], 9);
    }
    let original = memory(173);
    let fields = original.get_app_args();
    let written = app(
        "IRByteMemoryV1.mk",
        [
            fields[0].clone(),
            app(
                "ir_byte_write_word_v1",
                [
                    fields[1].clone(),
                    nat(source.address),
                    nat(8),
                    nat(source.address),
                ],
            ),
            fields[2].clone(),
        ],
    );
    app(
        "IRByteWorldV1.mk",
        [c("Nat"), written, nat(37), list("Nat", &[]), nat(9)],
    )
}

fn terminal(source: &PointerSource, world: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app(
                "IROutcome.ret",
                [list(
                    "IRScalar",
                    &[pointer(source.address.checked_add(source.advance).unwrap())],
                )],
            ),
            world,
        ],
    )
}

impl SourceTranslationModel for PointerModel {
    type Source = PointerSource;

    fn build_environment() -> Result<Environment, String> {
        LiteralReturnByteModel::build_environment()
    }

    fn reconstruct(source: &PointerSource, target: &Module) -> Result<Expr, String> {
        let reflected = reflect_core_module_v1(target, &[(source.function, 4096)])
            .map_err(|e| e.to_string())?;
        let function = reflected
            .function(source.function)
            .ok_or("missing pointer entry")?;
        let signature = target
            .func_type(function.ty)
            .ok_or("missing pointer signature")?;
        if signature.params != [source.ty.clone(), source.ty.clone()]
            || signature.returns != [Ty::Ptr]
        {
            return Err("source pointer signature differs from the actual target".into());
        }
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let initial = app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(u64::from(source.function.index())),
                list(
                    "IRScalar",
                    &[pointer(source.address), pointer(source.other)],
                ),
                memory(173),
                nat(37),
            ],
        );
        // Concrete source invocations, with a complete independently stated
        // world. No pointer type supplies live allocation or alias premises.
        Ok(eq(
            model.config_type(),
            model.run(
                &NatTerm::literal(if source.store {
                    4
                } else if source.advance == 0 {
                    3
                } else {
                    5
                }),
                initial,
            ),
            terminal(source, expected_world(source)),
        ))
    }
}

fn checker() -> &'static TranslationRechecker<PointerModel> {
    static CHECKER: OnceLock<TranslationRechecker<PointerModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn target(ty: Ty, advance: bool) -> (Module, PointerSource) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "pointer_transport",
        TargetInfo {
            triple: "aarch64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let tuple_id = if ty == Ty::RefMut(Box::new(tuple.clone())) {
        Some(builder.add_type(tuple.clone()))
    } else {
        None
    };
    let signature = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![Ty::Ptr]);
    let id = builder.declare_function("address", signature);
    let mut body = builder.define_function(id).unwrap();
    let block = body.create_block();
    let operand = body.add_block_param(block, ty.clone());
    let _other = body.add_block_param(block, ty.clone());
    body.switch_to_block(block);
    let copied = body.copy(ty.clone(), operand);
    let mut result = body.cast(CastOp::PtrToPtr, ty.clone(), Ty::Ptr, copied);
    if advance {
        let index = body.iconst(Ty::I64, 1);
        result = body.gep(tuple, result, vec![index]);
    }
    body.ret(vec![result]);
    body.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    if let Some(tuple_type) = tuple_id {
        module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type,
            size: 16,
            align: 8,
            field_offsets: vec![8, 0],
        });
    }
    assert!(crate_validation(&module).is_empty());
    (
        module,
        PointerSource {
            function: id,
            ty,
            address: 16,
            other: 24,
            advance: if advance { 16 } else { 0 },
            store: false,
        },
    )
}

fn crate_validation(module: &Module) -> Vec<trust_ir_build::ValidationError> {
    trust_ir_build::validate_module(module)
}

fn proof(source: &PointerSource, endpoint_world: Expr) -> Vec<u8> {
    // An untrusted reduction candidate. The real TranslationRechecker must
    // execute initialization, actual fetched Copy/Cast/GEP/Return and owner
    // retirement to check this against its independently reconstructed claim.
    let term = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [
            app("IRByteConfigV1", [c("Nat")]),
            terminal(source, endpoint_world),
        ],
    );
    trust_ir::proof::encode_clean_expr_v1(&term).unwrap()
}

fn rejects(source: &PointerSource, target: &Module, proof: &[u8]) {
    let error = checker().recheck(source, target, proof).unwrap_err();
    assert_eq!(error.stage(), "kernel audit", "{error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "semantic refusal required: {error}"
        );
    }
}

#[test]
fn typed_pointer_copy_cast_replays_complete_initial_and_terminal_worlds() {
    for ty in [
        Ty::Ref(Box::new(Ty::U64)),
        Ty::RefMut(Box::new(Ty::U64)),
        Ty::PtrConst(Box::new(Ty::U64)),
        Ty::PtrMut(Box::new(Ty::U64)),
        Ty::RefMut(Box::new(Ty::Tuple(vec![Ty::U8, Ty::U64]))),
    ] {
        let (module, mut source) = target(ty, false);
        for address in [16, 80, u64::MAX] {
            source.address = address;
            checker()
                .recheck(&source, &module, &proof(&source, world(173, 37, &[], 9)))
                .unwrap();
        }
    }
}

#[test]
fn tuple_pointer_gep_uses_the_actual_declared_layout_in_kernel_execution() {
    let (module, source) = target(Ty::RefMut(Box::new(Ty::Tuple(vec![Ty::U8, Ty::U64]))), true);
    let bytes = proof(&source, world(173, 37, &[], 9));
    checker().recheck(&source, &module, &bytes).unwrap();
    let mut changed = module.clone();
    changed.tuple_layouts[0].size = 32;
    assert!(crate_validation(&changed).is_empty());
    rejects(&source, &changed, &bytes);
}

#[test]
fn typed_pointer_replay_rejects_wrong_world_operands_and_unowned_store() {
    let (module, source) = target(Ty::RefMut(Box::new(Ty::U64)), false);
    let bytes = proof(&source, world(173, 37, &[], 9));
    checker().recheck(&source, &module, &bytes).unwrap();
    for endpoint_world in [
        world(174, 37, &[], 9),
        world(173, 38, &[], 9),
        world(173, 37, &[nat(8)], 9),
        world(173, 37, &[], 8),
    ] {
        rejects(&source, &module, &proof(&source, endpoint_world));
    }
    let mut changed = module.clone();
    let other = changed.functions[0].blocks[0].params[1].0;
    let Inst::Copy { operand, .. } = &mut changed.functions[0].blocks[0].body[0].inst else {
        panic!()
    };
    *operand = other;
    rejects(&source, &changed, &bytes);
    let mut changed_source = source.clone();
    changed_source.address = 80;
    rejects(&changed_source, &module, &bytes);
    // Address80 is a retired allocation in the real incoming world. A typed
    // RefMut carrier and an explicit cast cannot manufacture store access.
    let ptr = changed.functions[0].blocks[0].body[1].results[0];
    let mut store = module.clone();
    store.functions[0].blocks[0].body.insert(
        2,
        trust_ir::InstrNode::new(Inst::Store {
            ty: Ty::Ptr,
            ptr,
            value: ptr,
            volatile: false,
            align: Some(8),
        }),
    );
    assert!(crate_validation(&store).is_empty());
    let mut store_source = source.clone();
    store_source.store = true;
    checker()
        .recheck(
            &store_source,
            &store,
            &proof(&store_source, expected_world(&store_source)),
        )
        .unwrap();
    store_source.address = 80;
    rejects(
        &store_source,
        &store,
        &proof(&store_source, expected_world(&store_source)),
    );
}
