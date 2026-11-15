// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored SSA pointer-part fixtures, not a Rust/DST/ownership certificate.
//! Every scalar transfer is fetched from the actual module and the final
//! candidate is kernel-replayed against initialization and the whole world.

use super::*;
use trust_ir::{Block, FatPtrKind, FuncTy, Function, InstrNode, TyId, ValueId};
use trust_ir_build::core_execution::PendingEquality;

const FUNCTION: FuncId = FuncId::new(7);
const BLOCK: BlockId = BlockId::new(3);

fn kinds() -> [FatPtrKind; 6] {
    [
        FatPtrKind::Str,
        FatPtrKind::Slice(TyId(0)),
        FatPtrKind::TraitObject { trait_id: 91 },
        FatPtrKind::TraitObject { trait_id: 92 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ]
}
fn pointer(address: u64) -> Expr {
    if address == 0 {
        c("IRScalar.nullptr_")
    } else {
        app("IRScalar.ptr_", [nat(address)])
    }
}
fn metadata(kind: FatPtrKind, word: u64) -> Expr {
    if kind.metadata_ty(64) == Some(Ty::Ptr) {
        pointer(word)
    } else {
        app("IRScalar.int_", [nat(word)])
    }
}
fn fat(data: u64, metadata: u64) -> Expr {
    app("IRScalar.fat_", [nat(data), nat(metadata)])
}
fn fixture(kind: FatPtrKind) -> Module {
    let mut module = Module::new("authored_nominal_pointer_parts");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module.types.push(Ty::U8);
    let metadata_ty = kind.metadata_ty(64).unwrap();
    let ty = Ty::FatPtr(kind);
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, metadata_ty.clone(), Ty::Ptr, metadata_ty.clone()],
            returns: vec![Ty::Ptr, metadata_ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FUNCTION, "construct_and_split", signature, BLOCK);
    let mut block = Block::new(BLOCK);
    block.params = vec![
        (ValueId(19), Ty::Ptr),
        (ValueId(20), metadata_ty.clone()),
        (ValueId(21), Ty::Ptr),
        (ValueId(22), metadata_ty.clone()),
    ];
    for (data, metadata, destination) in [(19, 20, 30), (21, 22, 33)] {
        block.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: ty.clone(),
                metadata_ty: metadata_ty.clone(),
                data: ValueId(data),
                metadata: ValueId(metadata),
            })
            .with_result(ValueId(destination)),
        );
    }
    block.body.extend([
        InstrNode::new(Inst::PtrData {
            ptr_ty: ty.clone(),
            ptr: ValueId(30),
        })
        .with_result(ValueId(31)),
        InstrNode::new(Inst::PtrMetadata {
            ptr_ty: ty,
            metadata_ty,
            ptr: ValueId(30),
        })
        .with_result(ValueId(32)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(31), ValueId(32)],
        }),
    ]);
    function.blocks.push(block);
    module.functions.push(function);
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    module
}

#[derive(Clone, Copy)]
struct Claim {
    kind: FatPtrKind,
    data: u64,
    metadata: u64,
}
impl Claim {
    fn arguments(self) -> Expr {
        list(
            "IRScalar",
            &[
                pointer(self.data),
                metadata(self.kind, self.metadata),
                pointer(40),
                metadata(self.kind, 11),
            ],
        )
    }
    fn terminal(self, state: Expr) -> Expr {
        app(
            "IRByteConfigV1.halted",
            [
                c("Nat"),
                app(
                    "IROutcome.ret",
                    [list(
                        "IRScalar",
                        &[pointer(self.data), metadata(self.kind, self.metadata)],
                    )],
                ),
                state,
            ],
        )
    }
    fn initial(self, model: &MachineModel) -> Expr {
        app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(7),
                self.arguments(),
                memory(173),
                nat(37),
            ],
        )
    }
}
struct PartsModel;
impl SourceTranslationModel for PartsModel {
    type Source = Claim;
    fn build_environment() -> Result<Environment, String> {
        LiteralReturnByteModel::build_environment()
    }
    fn reconstruct(claim: &Claim, module: &Module) -> Result<Expr, String> {
        let reflected =
            reflect_core_module_v1(module, &[(FUNCTION, 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(5), claim.initial(&model)),
            claim.terminal(world(173, 37, &[], 9)),
        ))
    }
}
fn checker() -> &'static TranslationRechecker<PartsModel> {
    static CHECKER: OnceLock<TranslationRechecker<PartsModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}
fn truth(assembler: &mut Assembler<'_>, term: Expr) -> PendingEquality {
    assembler
        .conversion(c("Bool"), term, c("Bool.true"))
        .unwrap()
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Fault {
    None,
    Result,
    Carrier,
    Destination,
    Site,
    Pc,
    Legacy,
}
fn assemble(module: &Module, claim: Claim, fault: Fault, terminal: Option<Expr>) -> Vec<u8> {
    let reflected = reflect_core_module_v1(module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(FUNCTION).unwrap();
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let memory_guard = truth(&mut assembler, EntryTarget::memory_admission(memory(173)));
    let entry_guard = truth(
        &mut assembler,
        entry.admission(&model, claim.arguments()).unwrap(),
    );
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            claim.arguments(),
            memory(173),
            nat(37),
            memory_guard,
            entry_guard,
        )
        .unwrap();
    let mut current = initialized.current().clone();
    let original = current.clone();
    let mut valid = initialized.valid().clone();
    let mut prefix = assembler.zero(&model, current.running(&model)).unwrap();
    for pc in 0..4 {
        let mut site = catalog
            .fetch(Coordinate {
                function: FUNCTION,
                block: BLOCK,
                instruction: if pc == 3 && fault == Fault::Pc { 2 } else { pc },
            })
            .unwrap();
        let value = match pc {
            0 => fat(claim.data, claim.metadata),
            1 => fat(40, 11),
            2 => pointer(claim.data),
            _ if fault == Fault::Carrier => app("IRScalar.bool_", [c("Bool.true")]),
            _ => metadata(
                claim.kind,
                claim.metadata + u64::from(fault == Fault::Result),
            ),
        };
        if pc == 3 && fault == Fault::Destination {
            site.results = list("Nat", &[nat(97)]);
        }
        if pc == 3 && fault == Fault::Site {
            let mut fields: Vec<Expr> = site.site.get_app_args().into_iter().cloned().collect();
            fields[5] = list("IRTy", &[c("IRTy.bool_")]);
            site.site = app("IRByteSiteV1.mk", fields);
        }
        let checks = site.scalar_checks(&model, &current, value.clone()).unwrap();
        let evaluated = if pc == 3 && fault == Fault::Legacy {
            // The old evaluator erases vtable metadata to an integer. A reflexive
            // proof about that result cannot prove the typed Byte projection.
            let old = app("ir_ptrmeta_eval", [fat(claim.data, claim.metadata)]);
            let proof = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [c("IRStepResult"), old],
            );
            PendingEquality::candidate(
                c("IRStepResult"),
                checks.evaluation,
                app("IRStepResult.value", [value.clone()]),
                proof,
            )
        } else {
            assembler
                .conversion(
                    c("IRStepResult"),
                    checks.evaluation,
                    app("IRStepResult.value", [value.clone()]),
                )
                .unwrap()
        };
        let operands = truth(&mut assembler, checks.operands);
        let result = truth(&mut assembler, checks.result);
        let next = site
            .scalar_value(
                &mut assembler,
                &model,
                &current,
                value,
                ScalarPremises {
                    evaluated,
                    operands,
                    result,
                    before: valid,
                },
            )
            .unwrap();
        assert_eq!(next.current().world, original.world);
        assert_eq!(next.current().tail, original.tail);
        assert_eq!(next.current().legacy_memory, original.legacy_memory);
        assert_eq!(next.current().legacy_cursor, original.legacy_cursor);
        prefix = assembler.concatenate(prefix, next.run().clone()).unwrap();
        current = next.current().clone();
        valid = next.valid().clone();
    }
    let returning = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block: BLOCK,
            instruction: 4,
        })
        .unwrap();
    let dispatch = returning
        .step(&mut assembler, &model, &current, valid)
        .unwrap();
    let finish = assembler
        .conversion(
            model.config_type(),
            dispatch.right().clone(),
            terminal.unwrap_or_else(|| claim.terminal(world(173, 37, &[], 9))),
        )
        .unwrap();
    let step = assembler.compose(dispatch, finish).unwrap();
    let returned = assembler
        .one_step(&model, current.running(&model), step)
        .unwrap();
    let execution = assembler.concatenate(prefix, returned).unwrap();
    let mapped = assembler
        .congruence(
            initialized.equality().clone(),
            model.config_type(),
            |state| model.run(execution.fuel(), state),
        )
        .unwrap();
    let start = assembler
        .conversion(
            model.config_type(),
            model.run(&NatTerm::literal(5), claim.initial(&model)),
            mapped.left().clone(),
        )
        .unwrap();
    let end = assembler
        .conversion(
            model.config_type(),
            mapped.right().clone(),
            execution.equality().left().clone(),
        )
        .unwrap();
    let proof = assembler.compose(start, mapped).unwrap();
    let proof = assembler.compose(proof, end).unwrap();
    let proof = assembler
        .compose(proof, execution.equality().clone())
        .unwrap();
    let closed = scope.close(proof.term()).unwrap();
    assert!(
        !closed.has_fvar_quick(),
        "no evaluation or post-state assumptions"
    );
    trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap()
}
fn rejects(claim: &Claim, module: &Module, proof: &[u8]) {
    let error = checker().recheck_dag_v2(claim, module, proof).unwrap_err();
    assert_eq!(error.stage(), "kernel audit");
    assert!(error.reason().contains("TypeMismatch"), "{error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "{error}"
        );
    }
}

#[test]
fn all_nominal_fat_parts_replay_fetched_five_step_whole_world_including_null() {
    for kind in kinds() {
        let module = fixture(kind);
        let original = module.clone();
        for (data, metadata) in [(24, 7), (0, 0), (u64::MAX, u64::MAX)] {
            let claim = Claim {
                kind,
                data,
                metadata,
            };
            let proof = assemble(&module, claim, Fault::None, None);
            let checked = checker().recheck_dag_v2(&claim, &module, &proof).unwrap();
            assert!(std::ptr::eq(checked.target(), &module));
            assert!(std::ptr::eq(checked.source(), &claim));
        }
        assert_eq!(module, original);
    }
}

#[test]
fn fat_parts_fetched_result_carrier_destination_site_pc_and_legacy_are_bound() {
    let kind = FatPtrKind::ContainerVtable;
    let module = fixture(kind);
    let claim = Claim {
        kind,
        data: 24,
        metadata: 7,
    };
    for fault in [
        Fault::Result,
        Fault::Carrier,
        Fault::Destination,
        Fault::Site,
        Fault::Pc,
        Fault::Legacy,
    ] {
        rejects(&claim, &module, &assemble(&module, claim, fault, None));
    }
}

#[test]
fn fat_parts_live_ssa_operands_source_invocation_and_entire_world_are_bound() {
    for kind in [FatPtrKind::Str, FatPtrKind::TraitObject { trait_id: 91 }] {
        let module = fixture(kind);
        let claim = Claim {
            kind,
            data: 24,
            metadata: 7,
        };
        let proof = assemble(&module, claim, Fault::None, None);
        for mode in 0..4 {
            let mut changed = module.clone();
            let body = &mut changed.functions[0].blocks[0].body;
            match mode {
                0 => {
                    let Inst::PtrFromParts { data, .. } = &mut body[0].inst else {
                        unreachable!()
                    };
                    *data = ValueId(21);
                }
                1 => {
                    let Inst::PtrFromParts { metadata, .. } = &mut body[0].inst else {
                        unreachable!()
                    };
                    *metadata = ValueId(22);
                }
                2 => {
                    let Inst::PtrData { ptr, .. } = &mut body[2].inst else {
                        unreachable!()
                    };
                    *ptr = ValueId(33);
                }
                _ => {
                    let Inst::PtrMetadata { ptr, .. } = &mut body[3].inst else {
                        unreachable!()
                    };
                    *ptr = ValueId(33);
                }
            }
            assert!(trust_ir_build::validate_module(&changed).is_empty());
            rejects(&claim, &changed, &proof);
        }
        rejects(&Claim { data: 25, ..claim }, &module, &proof);
        rejects(
            &Claim {
                metadata: 8,
                ..claim
            },
            &module,
            &proof,
        );
        for wrong in [
            world(174, 37, &[], 9),
            world(173, 38, &[], 9),
            world(173, 37, &[nat(8)], 9),
            world(173, 37, &[], 8),
        ] {
            rejects(
                &claim,
                &module,
                &assemble(&module, claim, Fault::None, Some(claim.terminal(wrong))),
            );
        }
    }
}
