// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored diagnostic mirror of Trust's measured eight-node U64 wrapper.
//! The actual reflector and fetched assembler are used, but this fixture is
//! NOT a compiler-owned module or a Rust/Arc/concurrency refinement claim.
//! Pending obligations remain pending even after this closed sequential run.

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use std::sync::OnceLock;
use trust_ir::{
    AtomicRMWOp, Block, BlockId, CallingConv, CastOp, Constant, Endianness, FieldDef, FuncId,
    FuncTy, FuncTyId, Function, Inst, InstrNode, Linkage, Module, ObligationKind, ObligationSite,
    Ordering, Producer, ProofFormula, ProofId, ProofObligation, ProofObligationSourceIdentity,
    ProofObligationSourceRange, ProofStatus, StructDef, StructId, StructPassingPolicy, StructRepr,
    TargetInfo, Ty, ValueId,
};
use trust_ir_build::{
    core_execution::{
        Assembler, BranchPremises, Catalog, Coordinate, EntryTarget, Limits, MachineModel,
        MemoryPremises, MemoryResult, NatTerm, PendingEquality, ScalarPremises,
    },
    core_reflection::reflect_core_module_v1,
    scoped_local::LocalScope,
    translation::{SourceTranslationModel, TranslationProofEncoding, TranslationRechecker},
};

#[path = "core_execution_atomic_replay/usize.rs"]
mod usize_replay;

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn scalar(value: u64) -> Expr {
    app("IRScalar.int_", [nat(value)])
}
fn pointer(value: u64) -> Expr {
    app("IRScalar.ptr_", [nat(value)])
}
fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, value| {
            app("IRList.cons", [c(ty), value.clone(), tail])
        })
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, value],
    )
}
fn providers() -> Expr {
    let lam = |ty, body| Expr::lam(BinderInfo::Default, ty, body);
    lam(
        c("Nat"),
        lam(
            app("IRList", [c("IRScalar")]),
            lam(
                c("IRByteMemoryV1"),
                lam(
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

fn allocations() -> Expr {
    list(
        "IRByteAllocationV1",
        &[
            app(
                "IRByteAllocationV1.mk",
                [nat(16), nat(32), nat(0), c("Bool.true")],
            ),
            app(
                "IRByteAllocationV1.mk",
                [nat(80), nat(8), nat(7), c("Bool.false")],
            ),
        ],
    )
}
fn background(frame_word: u64) -> Expr {
    app(
        "ir_byte_write_word_v1",
        [
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                app("IROption.some", [c("Nat"), nat(173)]),
            ),
            nat(32),
            nat(8),
            nat(frame_word),
        ],
    )
}
fn memory_from(bytes: Expr) -> Expr {
    app("IRByteMemoryV1.mk", [allocations(), bytes, nat(128)])
}
fn memory(frame_word: u64) -> Expr {
    memory_from(app(
        "ir_byte_write_word_v1",
        [background(frame_word), nat(16), nat(8), nat(41)],
    ))
}
fn written(frame_word: u64, value: u64) -> Expr {
    memory_from(app(
        "ir_byte_write_word_v1",
        [
            app("ir_byte_mem_bytes_v1", [memory(frame_word)]),
            nat(16),
            nat(8),
            nat(value),
        ],
    ))
}

#[derive(Clone)]
struct Invocation {
    pointer: u64,
    old: u64,
    new: u64,
    frame_word: u64,
    host: u64,
    next_owner: u64,
    owners: Vec<Expr>,
}
impl Default for Invocation {
    fn default() -> Self {
        Self {
            pointer: 16,
            old: 41,
            new: 48,
            frame_word: 77,
            host: 37,
            next_owner: 9,
            owners: vec![],
        }
    }
}
fn terminal(invocation: &Invocation) -> Expr {
    // Independent complete postcondition, not copied from an assembler result.
    let world = app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            written(invocation.frame_word, invocation.new),
            nat(invocation.host),
            list("Nat", &invocation.owners),
            nat(invocation.next_owner),
        ],
    );
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app(
                "IROutcome.ret",
                [list("IRScalar", &[scalar(invocation.old)])],
            ),
            world,
        ],
    )
}
fn initial(model: &MachineModel, address: u64) -> Expr {
    app(
        "ir_byte_init_v1",
        [
            c("Nat"),
            model.context().clone(),
            nat(0),
            list("IRScalar", &[pointer(address)]),
            memory(77),
            nat(37),
        ],
    )
}
struct SequentialAtomicModel;
impl SourceTranslationModel for SequentialAtomicModel {
    type Source = Invocation;
    fn build_environment() -> Result<Environment, String> {
        Ok(shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|error| error.to_string())?
            .env()
            .clone())
    }
    fn reconstruct(source: &Invocation, target: &Module) -> Result<Expr, String> {
        let reflected = reflect_core_module_v1(target, &[(FuncId::new(0), 4096)])
            .map_err(|error| error.to_string())?;
        let function = reflected
            .function(FuncId::new(0))
            .ok_or("missing wrapper")?;
        let signature = target.func_type(function.ty).ok_or("missing signature")?;
        if signature.params != [Ty::Ptr] || signature.returns != [Ty::U64] {
            return Err("expected the measured scalar U64 wrapper signature".into());
        }
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(8), initial(&model, source.pointer)),
            terminal(source),
        ))
    }
}
fn checker() -> &'static TranslationRechecker<SequentialAtomicModel> {
    static CHECKER: OnceLock<TranslationRechecker<SequentialAtomicModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn fixture() -> Module {
    // Typed manual reproduction of the 2026-09-24 Trust module census. Source
    // strings below are retained DIAGNOSTICS, never authenticated by this test.
    let mut module = Module::new("relaxed_u64");
    module.target_info = Some(TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module.types.push(Ty::U8);
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::U64],
        abi: None,
        is_vararg: false,
    });
    for (id, (name, field, ty, repr)) in [
        (
            "core::sync::atomic::private::Align8",
            "0",
            Ty::U64,
            StructRepr::C,
        ),
        (
            "core::cell::UnsafeCell",
            "value",
            Ty::Struct(StructId::new(0)),
            StructRepr::Transparent,
        ),
        (
            "core::sync::atomic::Atomic",
            "v",
            Ty::Struct(StructId::new(1)),
            StructRepr::C,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        module.structs.push(StructDef {
            id: StructId::new(id as u32),
            name: name.into(),
            fields: vec![FieldDef {
                name: field.into(),
                ty,
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr,
            origin: None,
        });
    }
    let v = ValueId::new;
    let mut function = Function::new(
        FuncId::new(0),
        "relaxed_u64",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    function.calling_conv = CallingConv::C;
    function.linkage = Linkage::External;
    function.producer = Some(Producer::TrustIr);
    let mut first = Block::new(BlockId::new(0));
    first.params = vec![(v(0), Ty::Ptr)];
    first.body = [
        (
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
            vec![v(4)],
        ),
        (
            Inst::GEP {
                pointee_ty: Ty::Struct(StructId::new(1)),
                base: v(0),
                indices: vec![v(4)],
                inbounds: false,
            },
            vec![v(5)],
        ),
        (
            Inst::Copy {
                ty: Ty::Ptr,
                operand: v(5),
            },
            vec![v(6)],
        ),
        (
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Ptr,
                operand: v(6),
            },
            vec![v(7)],
        ),
        (
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(7),
            },
            vec![v(8)],
        ),
        (
            Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: Ty::U64,
                ptr: v(7),
                value: v(8),
                ordering: Ordering::Relaxed,
            },
            vec![v(9)],
        ),
        (
            Inst::Br {
                target: BlockId::new(1),
                args: vec![],
            },
            vec![],
        ),
    ]
    .into_iter()
    .map(|(inst, results)| InstrNode::new(inst).with_results(results))
    .collect();
    let mut last = Block::new(BlockId::new(1));
    last.body
        .push(InstrNode::new(Inst::Return { values: vec![v(9)] }));
    function.blocks = vec![first, last];
    module.functions.push(function);
    // Repository-relative: the measured span named a developer's checkout.
    // It is span metadata only; no assertion here depends on its spelling.
    let file = "library/core/src/sync/atomic.rs";
    module.files.push(file.into());
    for (index, (kind, class, native, requirement)) in [
        (ObligationKind::MemorySafety, "memory", 1369508422u32, "a live, initialized, writable, 8-byte-aligned u64 allocation"),
        (ObligationKind::Ownership, "ownership", 2901171305u32, "compatible atomic accesses and an explicit concurrent or exclusive sequential memory invariant"),
    ].into_iter().enumerate() {
        let source_id = format!("mir-atomic:{class}:compiler_atomic_bridge_fixture::relaxed_u64:bb0:terminator");
        let assertion_id = format!("trust-assertion:{source_id}");
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(index as u32), kind, status: ProofStatus::Pending,
            description: format!("compiler-authenticated relaxed xadd `core::intrinsics::atomic_xadd::<u64, u64, core::intrinsics::AtomicOrdering::Relaxed>` still requires {requirement}"),
            formula: Some(ProofFormula::new("trust.trust_ir.obligation-source.v1", serde_json::json!({
                "assertion_id": assertion_id, "native_assertion_id": native, "source_id": source_id,
                "span": {"file": file, "line_start": 3923, "line_end": 3923, "col_start": 23, "col_end": 81},
            }).to_string())),
            function: Some(FuncId::new(0)), source: Some(ProofObligationSourceIdentity::new(source_id, assertion_id)
                .with_range(ProofObligationSourceRange { file: 0, start_line: 3923, start_col: 23, end_line: 3923, end_col: 81 })),
            site: Some(ObligationSite::new(FuncId::new(0), BlockId::new(0), 5)), spec: None,
        });
    }
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn limits() -> Limits {
    Limits {
        max_operations: 4_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn truth(assembler: &mut Assembler<'_>, guard: Expr) -> PendingEquality {
    assembler
        .conversion(c("Bool"), guard, c("Bool.true"))
        .unwrap()
}
fn atomic_evaluation(context: Expr) -> Expr {
    let u64_ty = app("IRTy.uint_", [nat(64)]);
    let layout = app(
        "IRByteLayoutV1.mk",
        [u64_ty, nat(8), nat(8), list("IRTy", &[]), list("Nat", &[])],
    );
    app(
        "ir_byte_fetch_add_relaxed_u64_seq_below_v1",
        [
            context,
            memory(77),
            nat(16),
            nat(41),
            nat(7),
            app("Nat.le_add_right", [nat(17), nat(u64::MAX - 16)]),
            refl(
                app("IROption", [c("IRByteLayoutV1")]),
                app("IROption.some", [c("IRByteLayoutV1"), layout]),
            ),
            refl(c("Bool"), c("Bool.true")),
            app(
                "ir_byte_u64_rep_write_v1",
                [memory_from(background(77)), nat(16), nat(41)],
            ),
            app("Nat.le_add_right", [nat(49), nat(u64::MAX - 48)]),
        ],
    )
}

fn assemble(module: &Module, wrong_pc: bool, wrong_old: bool, wrong_destination: bool) -> Vec<u8> {
    assemble_with_evaluator(
        module,
        wrong_pc,
        wrong_old,
        wrong_destination,
        atomic_evaluation,
    )
}

fn assemble_with_evaluator(
    module: &Module,
    wrong_pc: bool,
    wrong_old: bool,
    wrong_destination: bool,
    atomic_evaluator: fn(Expr) -> Expr,
) -> Vec<u8> {
    let reflected = reflect_core_module_v1(module, &[(FuncId::new(0), 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(FuncId::new(0)).unwrap();
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let arguments = list("IRScalar", &[pointer(16)]);
    let memory_guard = truth(&mut assembler, EntryTarget::memory_admission(memory(77)));
    let entry_guard = truth(
        &mut assembler,
        entry.admission(&model, arguments.clone()).unwrap(),
    );
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            arguments,
            memory(77),
            nat(37),
            memory_guard,
            entry_guard,
        )
        .unwrap();
    let mut current = initialized.current().clone();
    let mut valid = initialized.valid().clone();
    let mut prefix = assembler.zero(&model, current.running(&model)).unwrap();
    for pc in 0..6 {
        let fetched_pc = if wrong_pc && pc == 5 { 1 } else { pc };
        let mut site = catalog
            .fetch(Coordinate {
                function: FuncId::new(0),
                block: BlockId::new(0),
                instruction: fetched_pc,
            })
            .unwrap();
        if wrong_destination && pc == 5 {
            // Corrupt only the untrusted candidate's result binding. The
            // catalog's actual node remains unchanged and must refute it.
            site.results = list("Nat", &[nat(10)]);
        }
        let transfer = if pc == 1 || pc == 5 {
            let result = MemoryResult {
                value: if pc == 1 {
                    pointer(16)
                } else {
                    scalar(if wrong_old { 48 } else { 41 })
                },
                memory: if pc == 1 { memory(77) } else { written(77, 48) },
            };
            let checks = site.memory_checks(&model, &current, &result).unwrap();
            let evaluated = if pc == 5 {
                // The primitive theorem derives the result from bytes/layout/
                // access/bounds. The enclosing kernel replay checks that this
                // very evaluator uses the fetched operands and current memory.
                PendingEquality::candidate(
                    c("IRByteMemoryResultV1"),
                    checks.evaluation,
                    result.result(),
                    atomic_evaluator(model.context().clone()),
                )
            } else {
                assembler
                    .conversion(
                        c("IRByteMemoryResultV1"),
                        checks.evaluation,
                        result.result(),
                    )
                    .unwrap()
            };
            let guard = truth(&mut assembler, checks.result);
            let allocations = assembler
                .conversion(
                    app("IRList", [c("IRByteAllocationV1")]),
                    app("ir_byte_mem_allocs_v1", [result.memory.clone()]),
                    app(
                        "ir_byte_mem_allocs_v1",
                        [app(
                            "ir_byte_world_memory_v1",
                            [c("Nat"), current.world.clone()],
                        )],
                    ),
                )
                .unwrap();
            let transferred = site
                .memory_value(
                    &mut assembler,
                    &model,
                    &current,
                    result,
                    MemoryPremises {
                        evaluated,
                        result: guard,
                        allocations,
                        before: valid.clone(),
                    },
                )
                .unwrap();
            (
                transferred.current().clone(),
                transferred.valid().clone(),
                transferred.run().clone(),
            )
        } else {
            let value = match pc {
                0 => scalar(0),
                2 | 3 => pointer(16),
                4 => scalar(7),
                _ => unreachable!(),
            };
            let checks = site.scalar_checks(&model, &current, value.clone()).unwrap();
            let evaluated = assembler
                .conversion(
                    c("IRStepResult"),
                    checks.evaluation,
                    app("IRStepResult.value", [value.clone()]),
                )
                .unwrap();
            let operands = truth(&mut assembler, checks.operands);
            let result = truth(&mut assembler, checks.result);
            let transferred = site
                .scalar_value(
                    &mut assembler,
                    &model,
                    &current,
                    value,
                    ScalarPremises {
                        evaluated,
                        operands,
                        result,
                        before: valid.clone(),
                    },
                )
                .unwrap();
            (
                transferred.current().clone(),
                transferred.valid().clone(),
                transferred.run().clone(),
            )
        };
        (current, valid) = (transfer.0, transfer.1);
        prefix = assembler.concatenate(prefix, transfer.2).unwrap();
    }
    let branching = catalog
        .fetch(Coordinate {
            function: FuncId::new(0),
            block: BlockId::new(0),
            instruction: 6,
        })
        .unwrap();
    let target = catalog
        .branch_target(FuncId::new(0), BlockId::new(1))
        .unwrap();
    let checks = branching
        .branch_checks(&model, &current, &target, None)
        .unwrap();
    let resolved = assembler
        .conversion(
            app("IRList", [c("IRScalar")]),
            app("ir_resolve", [current.machine(), checks.arguments]),
            list("IRScalar", &[]),
        )
        .unwrap();
    let arity = truth(&mut assembler, checks.arity);
    let branched = branching
        .branch_to(
            &mut assembler,
            &model,
            &current,
            &target,
            None,
            BranchPremises {
                condition: None,
                resolved,
                arity,
                before: valid,
            },
        )
        .unwrap();
    prefix = assembler
        .concatenate(prefix, branched.run().clone())
        .unwrap();
    let returning = catalog
        .fetch(Coordinate {
            function: FuncId::new(0),
            block: BlockId::new(1),
            instruction: 0,
        })
        .unwrap();
    let dispatch = returning
        .step(
            &mut assembler,
            &model,
            branched.current(),
            branched.valid().clone(),
        )
        .unwrap();
    let finish = assembler
        .conversion(
            model.config_type(),
            dispatch.right().clone(),
            terminal(&Invocation::default()),
        )
        .unwrap();
    let step = assembler.compose(dispatch, finish).unwrap();
    let run = assembler
        .one_step(&model, branched.current().running(&model), step)
        .unwrap();
    let execution = assembler.concatenate(prefix, run).unwrap();
    let initialized_run = assembler
        .congruence(
            initialized.equality().clone(),
            model.config_type(),
            |state| model.run(execution.fuel(), state),
        )
        .unwrap();
    let start = assembler
        .conversion(
            model.config_type(),
            model.run(&NatTerm::literal(8), initial(&model, 16)),
            initialized_run.left().clone(),
        )
        .unwrap();
    let middle = assembler
        .conversion(
            model.config_type(),
            initialized_run.right().clone(),
            execution.equality().left().clone(),
        )
        .unwrap();
    let complete = assembler.compose(start, initialized_run).unwrap();
    let complete = assembler.compose(complete, middle).unwrap();
    let complete = assembler
        .compose(complete, execution.equality().clone())
        .unwrap();
    let closed = scope.close(complete.term()).unwrap();
    assert!(
        !closed.has_fvar_quick(),
        "no successful-evaluation or post-world premise may remain free"
    );
    // The eight-step proof shares whole contexts/worlds. Preserve that sharing
    // with the existing explicit DAG carrier; do not raise tree-decoder limits.
    trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap()
}

fn rejects(source: &Invocation, module: &Module, proof: &[u8]) {
    let error = checker().recheck_dag_v2(source, module, proof).unwrap_err();
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
fn whole_u64_wrapper_replays_representation_derived_atomic_and_terminal_world() {
    let module = fixture();
    let before = module.clone();
    let invocation = Invocation::default();
    let proof = assemble(&module, false, false, false);
    let checked = checker()
        .recheck_dag_v2(&invocation, &module, &proof)
        .unwrap();
    assert!(std::ptr::eq(checked.target(), &module));
    assert!(std::ptr::eq(checked.source(), &invocation));
    assert_eq!(checked.proof_term(), proof);
    assert_eq!(
        checked.proof_encoding(),
        TranslationProofEncoding::LosslessDagV2
    );
    assert_eq!(
        module, before,
        "replay never changes target claims or ABI policy"
    );
    assert!(
        module
            .proof_obligations
            .iter()
            .all(|row| row.status == ProofStatus::Pending)
    );
    assert!(module.proof_certificates.is_empty());
}

#[test]
fn whole_u64_wrapper_rejects_wrong_result_world_and_live_pointer() {
    let module = fixture();
    let proof = assemble(&module, false, false, false);
    for changed in [
        Invocation {
            old: 48,
            ..Invocation::default()
        },
        Invocation {
            new: 41,
            ..Invocation::default()
        },
        Invocation {
            frame_word: 78,
            ..Invocation::default()
        },
        Invocation {
            host: 38,
            ..Invocation::default()
        },
        Invocation {
            next_owner: 8,
            ..Invocation::default()
        },
        Invocation {
            owners: vec![nat(8)],
            ..Invocation::default()
        },
        // Both 16 and 32 are live/aligned/initialized in the SAME initial memory.
        Invocation {
            pointer: 32,
            ..Invocation::default()
        },
    ] {
        rejects(&changed, &module, &proof);
    }
}

#[test]
fn whole_u64_wrapper_rejects_false_atomic_result_destination_and_fetched_pc() {
    let module = fixture();
    for (pc, old, destination) in [
        (true, false, false),
        (false, true, false),
        (false, false, true),
    ] {
        rejects(
            &Invocation::default(),
            &module,
            &assemble(&module, pc, old, destination),
        );
    }
}

#[test]
fn whole_u64_wrapper_rejects_changed_actual_module_and_layout() {
    let module = fixture();
    let proof = assemble(&module, false, false, false);
    let mut changed = module.clone();
    changed.functions[0].blocks[0].body[4].inst = Inst::Const {
        ty: Ty::U64,
        value: Constant::Int(8),
    };
    rejects(&Invocation::default(), &changed, &proof);
    let mut changed = module.clone();
    changed.functions[0].blocks[1].body[0].inst = Inst::Return {
        values: vec![ValueId::new(8)],
    };
    assert!(trust_ir_build::validate_module(&changed).is_empty());
    rejects(&Invocation::default(), &changed, &proof);
    let mut changed = module.clone();
    changed.structs[1].fields[0].offset = Some(8);
    assert!(reflect_core_module_v1(&changed, &[(FuncId::new(0), 4096)]).is_err());
}
