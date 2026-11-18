// Copyright 2026 Andrew Yates | Apache-2.0
//! Independently authored byte effects versus an actual ordinary Core body.
#![cfg(feature = "source-value-operational")]

use trust_ir::proof::{
    IslandEnvironment, ProofLineageId, ProofLineageManifest, ProofTransform, ProofTransformStage,
    SourceDefinitionRef, encode_island_declarations_v1,
};
use trust_ir::{
    BodyGate, CallingConv, Endianness, FuncId, GateEvidence, Inst, Module, ProofId, TargetInfo, Ty,
};
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Level, Name, env::Declaration};
use trust_ir_build::source_byte_entry::{ByteEntryRole, check_byte_entry_source};
use trust_ir_build::{
    ModuleBuilder, ValidationConfig, certify_source_bound_byte_entry,
    lineage_closed_with_validated_authority, validate_module_for_codegen,
    validate_module_with_config,
};

fn c(n: &str) -> Expr {
    Expr::const_str(n)
}
fn a(n: &str, xs: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(n), xs)
}
fn lam(t: Expr, b: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, t, b)
}
fn word(lane: u64, mutation: Mutation) -> Expr {
    if matches!(mutation, Mutation::MixedTypes) && lane == 0 {
        c("IRTy.ptr_")
    } else {
        a(
            if matches!(mutation, Mutation::MixedTypes) && lane == 2 {
                "IRTy.int_"
            } else {
                "IRTy.uint_"
            },
            [Expr::nat_lit(64)],
        )
    }
}
fn domains() -> [Expr; 4] {
    [
        c("IRByteContextV1"),
        c("IRByteMemoryV1"),
        c("Nat"),
        c("Nat"),
    ]
}
fn effect_type() -> Expr {
    domains()
        .into_iter()
        .rev()
        .fold(c("IRByteMemoryResultV1"), |b, t| {
            Expr::pi(BinderInfo::Default, t, b)
        })
}

// A source program written without reading a Module or target denotation:
// read each of five context words, then store that word to its output lane.
// Faults stop immediately and retain the actual fault memory, including earlier
// completed writes. The source returns unit, never a fabricated scalar status.
#[derive(Clone, Copy)]
enum Mutation {
    None,
    MixedTypes,
    DeadInboundsGep,
    ReadNext,
    OmitLastStore,
    EraseFault,
}
fn source(mutation: Mutation) -> IslandEnvironment {
    fn bind(op: Expr, good: Expr, mutation: Mutation) -> Expr {
        let failure = if matches!(mutation, Mutation::EraseFault) {
            a(
                "IRByteMemoryResultV1.value",
                [c("IRScalar.unit_"), Expr::bvar(0)],
            )
        } else {
            a("IRByteMemoryResultV1.fault", [Expr::bvar(1), Expr::bvar(0)])
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("IRByteMemoryResultV1.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                lam(c("IRByteMemoryResultV1"), c("IRByteMemoryResultV1")),
                lam(c("IRScalar"), lam(c("IRByteMemoryV1"), good)),
                lam(c("IROutcome"), lam(c("IRByteMemoryV1"), failure)),
                op,
            ],
        )
    }
    fn gep(ctx: Expr, mem: Expr, ptr: Expr, offset: u64) -> Expr {
        a(
            "ir_byte_gep_typed_v1",
            [
                ctx,
                a("IRTy.int_", [Expr::nat_lit(8)]),
                ptr,
                a(
                    "ir_byte_gep_typed_index_v1",
                    [
                        a("IRTy.int_", [Expr::nat_lit(64)]),
                        a("IRScalar.int_", [Expr::nat_lit(offset)]),
                    ],
                ),
                c("Bool.false"),
                mem,
            ],
        )
    }
    fn lane(n: u64, ctx: Expr, mem: Expr, input: Expr, output: Expr, mutation: Mutation) -> Expr {
        if n == 5 {
            if matches!(mutation, Mutation::DeadInboundsGep) {
                let operation = a(
                    "ir_byte_gep_typed_v1",
                    [
                        ctx,
                        a("IRTy.int_", [Expr::nat_lit(8)]),
                        input,
                        a(
                            "ir_byte_gep_typed_index_v1",
                            [
                                a("IRTy.int_", [Expr::nat_lit(64)]),
                                a("IRScalar.int_", [Expr::nat_lit(64)]),
                            ],
                        ),
                        c("Bool.true"),
                        mem,
                    ],
                );
                return bind(
                    operation,
                    a(
                        "IRByteMemoryResultV1.value",
                        [c("IRScalar.unit_"), Expr::bvar(0)],
                    ),
                    mutation,
                );
            }
            return a("IRByteMemoryResultV1.value", [c("IRScalar.unit_"), mem]);
        }
        fn read_store(
            n: u64,
            ctx: Expr,
            mem: Expr,
            original: [Expr; 2],
            addresses: [Expr; 2],
            mutation: Mutation,
        ) -> Expr {
            let [input, output] = addresses;
            let load = a(
                "ir_byte_load_v1",
                [
                    ctx.clone(),
                    word(n, mutation),
                    input,
                    Expr::nat_lit(8),
                    c("Bool.false"),
                    mem,
                ],
            );
            let after_load = if n == 4 && matches!(mutation, Mutation::OmitLastStore) {
                lane(
                    n + 1,
                    ctx.lift(2),
                    Expr::bvar(0),
                    c("IRScalar.nullptr_"),
                    output.lift(2),
                    mutation,
                )
            } else {
                let store = a(
                    "ir_byte_store_v1",
                    [
                        ctx.lift(2),
                        word(n, mutation),
                        output.lift(2),
                        Expr::bvar(1),
                        Expr::nat_lit(8),
                        c("Bool.false"),
                        Expr::bvar(0),
                    ],
                );
                bind(
                    store,
                    lane(
                        n + 1,
                        ctx.lift(4),
                        Expr::bvar(0),
                        original[0].lift(4),
                        original[1].lift(4),
                        mutation,
                    ),
                    mutation,
                )
            };
            bind(load, after_load, mutation)
        }
        // Reconstruct original parameter references by their lexical depth.
        // Every prior lane adds four successful binders (eight for n>0).
        if n == 0 && !matches!(mutation, Mutation::ReadNext) {
            read_store(
                n,
                ctx,
                mem,
                [input.clone(), output.clone()],
                [input, output],
                mutation,
            )
        } else {
            let delta = if n == 0 { 8 } else { n * 8 };
            let input_gep = gep(ctx.clone(), mem.clone(), input.clone(), delta);
            let output_gep = gep(ctx.lift(2), Expr::bvar(0), output.lift(2), n * 8);
            // After two GEP results, restore the original context/output
            // addresses for the recursive next lane through explicit arguments.
            let loaded = read_store(
                n,
                ctx.lift(4),
                Expr::bvar(0),
                [input.lift(4), output.lift(4)],
                [Expr::bvar(3), Expr::bvar(1)],
                mutation,
            );
            bind(input_gep, bind(output_gep, loaded, mutation), mutation)
        }
    }
    let body = lane(
        0,
        Expr::bvar(3),
        Expr::bvar(2),
        a("IRScalar.ptr_", [Expr::bvar(1)]),
        a("IRScalar.ptr_", [Expr::bvar(0)]),
        mutation,
    );
    let value = domains().into_iter().rev().fold(body, |b, t| lam(t, b));
    IslandEnvironment::new(
        encode_island_declarations_v1(&[Declaration::Definition {
            name: Name::from_string("Source.copyFive"),
            level_params: vec![],
            type_: effect_type(),
            value,
            is_reducible: true,
        }])
        .unwrap(),
    )
}

fn module() -> Module {
    module_typed(false, false)
}
fn module_typed(mixed: bool, dead_gep: bool) -> Module {
    let mut m = ModuleBuilder::new_with_target_info(
        "closed_context_output",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("darwinpcs".into()),
            struct_passing: Default::default(),
        },
    );
    let signature = m.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![]);
    let mut f = m.function("copy_five", signature);
    f.set_calling_conv(CallingConv::C);
    let block = f.create_block();
    let input = f.add_block_param(block, Ty::Ptr);
    let output = f.add_block_param(block, Ty::Ptr);
    f.switch_to_block(block);
    for n in 0..5 {
        let (ip, op) = if n == 0 {
            (input, output)
        } else {
            (
                f.gep_byte_offset(input, n * 8),
                f.gep_byte_offset(output, n * 8),
            )
        };
        let ty = if mixed && n == 0 {
            Ty::Ptr
        } else if mixed && n == 2 {
            Ty::I64
        } else {
            Ty::U64
        };
        let value = f.load_aligned(ty.clone(), ip, 8);
        f.store_aligned(ty, op, value, 8);
    }
    if dead_gep {
        let index = f.iconst(Ty::I64, 64);
        f.gep_inbounds(Ty::I8, input, vec![index]);
    }
    f.ret(vec![]);
    f.build();
    m.build().unwrap()
}
fn mint(
    m: &Module,
    island: &IslandEnvironment,
) -> Result<trust_ir_build::SourceBoundCallCertificates, String> {
    certify_source_bound_byte_entry(
        m,
        ProofLineageId::new(10),
        ProofId::new(20),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "byte-entry",
            "independent-source",
            "1",
        ),
        island,
        &[(
            m.functions[0].id,
            SourceDefinitionRef {
                decl: "Source.copyFive".into(),
                closure_digest: island.digest,
            },
        )],
    )
}
fn attach(
    m: &mut Module,
    rows: trust_ir_build::SourceBoundCallCertificates,
) -> ProofLineageManifest {
    let manifest = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        roots: rows.nodes.iter().map(|n| n.id).collect(),
        nodes: rows.nodes,
    };
    m.proof_obligations.extend(rows.obligations);
    m.proof_certificates.extend(rows.certificates);
    rebind_body(m);
    manifest
}
fn rebind_body(m: &mut Module) {
    let f = m.functions[0].id;
    let body_digest = m.function_body_digest(f).unwrap();
    m.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: Some(GateEvidence {
            obligation: ProofId::new(20),
            body_digest,
        }),
    });
}
fn config() -> ValidationConfig<'static> {
    ValidationConfig::pinned()
        .with_bound_certificates(true)
        .with_source_bound_certificates(true)
        .with_gate_evidence(true)
}

#[test]
fn whole_void_effect_replays_and_exports_exact_actual_typed_footprint() {
    let mut m = module();
    let rows = mint(&m, &source(Mutation::None)).unwrap();
    let manifest = attach(&mut m, rows);
    let report = validate_module_with_config(&m, &config());
    assert!(report.is_ok(), "{:?}", report.errors());
    let owner = check_byte_entry_source(&report).unwrap();
    assert!(std::ptr::eq(owner.module(), &m));
    assert_eq!(owner.function(), m.functions[0].id);
    assert_eq!(owner.function_in(&m), Ok(m.functions[0].id));
    assert!(owner.function_in(&m.clone()).is_err());
    assert_eq!(owner.accesses().len(), 10);
    assert_eq!(owner.addresses().len(), 8);
    for (lane, pair) in owner.accesses().as_chunks::<2>().0.iter().enumerate() {
        assert_eq!(
            (pair[0].role(), pair[1].role()),
            (ByteEntryRole::Context, ByteEntryRole::Output)
        );
        assert!(!pair[0].is_write() && pair[1].is_write());
        for access in pair {
            assert_eq!(access.offset(), lane as u64 * 8);
            assert_eq!(access.alignment(), 8);
            assert_eq!(access.ty(), &Ty::U64);
        }
    }
    assert!(validate_module_for_codegen(&m).is_empty());
    assert_eq!(
        lineage_closed_with_validated_authority(&m, &manifest),
        Ok(())
    );
}

#[test]
fn changed_read_store_or_fault_function_cannot_receive_source_license() {
    for change in [
        Mutation::ReadNext,
        Mutation::OmitLastStore,
        Mutation::EraseFault,
    ] {
        let error = mint(&module(), &source(change)).unwrap_err();
        eprintln!(
            "whole-effect semantic control: {}",
            error.chars().take(500).collect::<String>()
        );
        assert!(
            error.contains("TypeMismatch"),
            "semantic control must fail by actual kernel type mismatch: {error}"
        );
    }
}

#[test]
fn pointer_signed_and_unsigned_words_preserve_exact_original_lanes() {
    let mut m = module_typed(true, false);
    let rows = mint(&m, &source(Mutation::MixedTypes)).unwrap();
    attach(&mut m, rows);
    let report = validate_module_with_config(&m, &config());
    assert!(report.is_ok(), "{:?}", report.errors());
    let owner = check_byte_entry_source(&report).unwrap();
    for (accesses, expected) in owner.accesses().as_chunks::<2>().0.iter().zip([
        Ty::Ptr,
        Ty::U64,
        Ty::I64,
        Ty::U64,
        Ty::U64,
    ]) {
        assert_eq!(accesses[0].ty(), &expected);
        assert_eq!(accesses[1].ty(), &expected);
    }
    assert!(m.func_types[0].returns.is_empty());
}

#[test]
fn scalar_return_or_wrong_pointer_signature_is_not_a_byte_entry() {
    for change in 0..2 {
        let mut m = module();
        if change == 0 {
            m.func_types[0].returns = vec![Ty::U64];
        } else {
            m.func_types[0].params[0] = Ty::U64;
        }
        let error = mint(&m, &source(Mutation::None)).unwrap_err();
        assert!(error.contains("C(Ptr,Ptr)->void"), "{error}");
    }
}

#[test]
fn unused_foreign_signature_or_type_rows_are_not_covered_by_the_closed_profile() {
    for change in 0..2 {
        let mut m = module();
        if change == 0 {
            m.add_func_type(trust_ir::FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .unwrap();
        } else {
            m.types.push(Ty::U128);
        }
        let error = mint(&m, &source(Mutation::None)).unwrap_err();
        assert!(error.contains("complete closed primitive"), "{error}");
    }
}

#[test]
fn unused_inbounds_pointer_requirement_is_retained_beyond_access_roster() {
    let mut m = module_typed(false, true);
    let rows = mint(&m, &source(Mutation::DeadInboundsGep)).unwrap();
    attach(&mut m, rows);
    let report = validate_module_with_config(&m, &config());
    assert!(report.is_ok(), "{:?}", report.errors());
    let owner = check_byte_entry_source(&report).unwrap();
    assert_eq!(owner.accesses().len(), 10);
    assert_eq!(owner.addresses().len(), 9);
    let address = owner.addresses().last().unwrap();
    assert_eq!(
        (
            address.role(),
            address.base_offset(),
            address.offset(),
            address.is_inbounds()
        ),
        (ByteEntryRole::Context, 0, 64, true)
    );
    assert!(
        owner
            .accesses()
            .iter()
            .all(|access| access.offset() + 8 <= 40)
    );
    // The easier source omits a real possibly-faulting inbounds operation.
    m.functions[0].body_gate = None;
    m.proof_obligations.clear();
    m.proof_certificates.clear();
    let error = mint(&m, &source(Mutation::None)).unwrap_err();
    assert!(error.contains("TypeMismatch"), "{error}");
}

#[test]
fn body_return_role_and_source_certificate_mutations_refuse() {
    let mut original = module();
    let rows = mint(&original, &source(Mutation::None)).unwrap();
    attach(&mut original, rows);
    for mutation in 0..5 {
        let mut m = original.clone();
        match mutation {
            0 => {
                let context = m.functions[0].blocks[0].params[0].0;
                if let Inst::Store { ptr, .. } = &mut m.functions[0].blocks[0].body[1].inst {
                    *ptr = context;
                } else {
                    panic!("store roster changed")
                }
            }
            1 => {
                if let Inst::Return { values } =
                    &mut m.functions[0].blocks[0].body.last_mut().unwrap().inst
                {
                    values.push(trust_ir::ValueId::new(2));
                }
            }
            2 => m.proof_certificates.clear(),
            3 => {
                m.proof_certificates[0].evidence =
                    trust_ir::proof::ProofEvidence::InheritedFromCallee {
                        callee: FuncId::new(99),
                        obligation: ProofId::new(20),
                        external: None,
                    }
            }
            4 => {
                let output = m.functions[0].blocks[0].params[1].0;
                if let Inst::Load { ptr, .. } = &mut m.functions[0].blocks[0].body[0].inst {
                    *ptr = output;
                }
            }
            _ => unreachable!(),
        }
        rebind_body(&mut m);
        let report = validate_module_with_config(&m, &config());
        assert!(!report.is_ok(), "mutation{mutation} accepted");
        assert!(check_byte_entry_source(&report).is_err());
    }
}
