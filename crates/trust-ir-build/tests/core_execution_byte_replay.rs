// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual byte-vocabulary replay through the public execution assembler.
//!
//! Unlike the assembler's structural unit fixtures, every symbol here belongs
//! to Clean's shared ByteV1 vocabulary. No program-specific theorem, axiom or
//! evaluator replacement is installed. Checked arithmetic explicitly opts into
//! shared, checked product/restoring-division agreement laws. The basic source returns a literal,
//! with optional typed Copy transport. Its claim includes initialization and the
//! whole terminal memory/provider world,
//! fresh activation ownership and return retirement, not a projected value.
//! This establishes this bounded model's replay path, not TLA or native authority.

#[path = "core_execution_byte_replay/pointer.rs"]
mod typed_pointer;

#[path = "core_execution_byte_replay/pointer_cmp.rs"]
mod pointer_cmp;

#[path = "core_execution_byte_replay/scalar_cmp.rs"]
mod scalar_cmp;

#[path = "core_execution_byte_replay/usize_cmp.rs"]
mod usize_cmp;

#[path = "core_execution_byte_replay/canonical_scalar.rs"]
mod canonical_scalar;

#[path = "core_execution_byte_replay/rust_layout.rs"]
mod rust_layout;

#[path = "core_execution_byte_replay/insert_field.rs"]
mod insert_field;

#[path = "core_execution_byte_replay/fat_pointer.rs"]
mod fat_pointer;

#[path = "core_execution_byte_replay/overflow.rs"]
mod overflow;

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use std::sync::OnceLock;
use trust_ir::{
    BlockId, Constant, Endianness, FuncId, Inst, Module, StructPassingPolicy, TargetInfo, Ty,
};
use trust_ir_build::{
    ModuleBuilder,
    core_execution::{
        Assembler, Catalog, Coordinate, EntryTarget, Limits, MachineModel, NatTerm, ScalarPremises,
    },
    core_reflection::reflect_core_module_v1,
    scoped_local::LocalScope,
    translation::{SourceTranslationModel, TranslationRechecker},
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

fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, value| {
            app("IRList.cons", [c(ty), value.clone(), tail])
        })
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}

fn providers() -> Expr {
    // No imports exist. Nevertheless bind a real, total provider rather than
    // an undefined fixture name: any accidental call returns stuck/no_func.
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

fn memory(byte: u64) -> Expr {
    // A live external allocation and historical retired owner7. Initialization
    // must choose owner8 (not1), then preserve next9 after the root returns.
    let rows = list(
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
    );
    app(
        "IRByteMemoryV1.mk",
        [
            rows,
            lam(c("Nat"), app("IROption.some", [c("Nat"), nat(byte)])),
            nat(128),
        ],
    )
}

fn world(byte: u64, host: u64, owners: &[Expr], next: u64) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            memory(byte),
            nat(host),
            list("Nat", owners),
            nat(next),
        ],
    )
}

fn halted(value: u64, terminal_world: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app(
                "IROutcome.ret",
                [list("IRScalar", &[app("IRScalar.int_", [nat(value)])])],
            ),
            terminal_world,
        ],
    )
}

fn expected_terminal(value: u64) -> Expr {
    // Independently stated from the source invocation, never copied from an
    // assembler endpoint or obtained by normalizing the target execution.
    halted(value, world(173, 37, &[], 9))
}

fn initial(model: &MachineModel, function: FuncId) -> Expr {
    app(
        "ir_byte_init_v1",
        [
            c("Nat"),
            model.context().clone(),
            nat(u64::from(function.index())),
            list("IRScalar", &[]),
            memory(173),
            nat(37),
        ],
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

fn target(value: u64) -> (Module, FuncId, BlockId) {
    target_with_copies(value, 0)
}

fn target_with_copies(value: u64, copies: u32) -> (Module, FuncId, BlockId) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "byte_literal_return",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![], vec![Ty::U64]);
    let function_id = builder.declare_function("literal_return", signature);
    let block_id;
    {
        let mut function = builder.define_function(function_id).unwrap();
        block_id = function.create_block();
        function.switch_to_block(block_id);
        let mut result = function.uconst(Ty::U64, u128::from(value));
        for _ in 0..copies {
            result = function.copy(Ty::U64, result);
        }
        function.ret(vec![result]);
        function.build();
    }
    (
        builder.build().expect("ModuleBuilder::build: test fixture"),
        function_id,
        block_id,
    )
}

#[derive(Clone, Copy)]
struct LiteralReturn {
    function: FuncId,
    value: u64,
    copies: u32,
}

struct LiteralReturnByteModel;

impl SourceTranslationModel for LiteralReturnByteModel {
    type Source = LiteralReturn;

    fn build_environment() -> Result<Environment, String> {
        // TranslationRechecker owns its options. One environment-map clone per
        // checker shares immutable theorem DAGs from the once-built vocabulary;
        // no per-program reconstruction of the semantics or new declarations.
        Ok(shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|e| e.to_string())?
            .env()
            .clone())
    }

    fn reconstruct(source: &LiteralReturn, target: &Module) -> Result<Expr, String> {
        let reflected = reflect_core_module_v1(target, &[(source.function, 4096)])
            .map_err(|e| e.to_string())?;
        if reflected.function(source.function).is_none() {
            return Err("literal-return entry is absent".into());
        }
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        Ok(eq(
            model.config_type(),
            model.run(
                &NatTerm::literal(2 + u64::from(source.copies)),
                initial(&model, source.function),
            ),
            expected_terminal(source.value),
        ))
    }
}

fn checker() -> &'static TranslationRechecker<LiteralReturnByteModel> {
    static CHECKER: OnceLock<TranslationRechecker<LiteralReturnByteModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

struct Candidate {
    proof_bytes: Vec<u8>,
    initialized_world: Expr,
    returned_world: Expr,
}

fn assemble(
    module: &Module,
    function: FuncId,
    block: BlockId,
    terminal_override: Option<Expr>,
    wrong_return_pc: bool,
    false_scalar_value: bool,
) -> Candidate {
    assemble_with_copy_fault(
        module,
        function,
        block,
        terminal_override,
        wrong_return_pc,
        false_scalar_value,
        false,
    )
}

fn assemble_with_copy_fault(
    module: &Module,
    function: FuncId,
    block: BlockId,
    terminal_override: Option<Expr>,
    wrong_return_pc: bool,
    false_scalar_value: bool,
    false_copy_value: bool,
) -> Candidate {
    let reflected = reflect_core_module_v1(module, &[(function, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(function).unwrap();
    let constant = catalog
        .fetch(Coordinate {
            function,
            block,
            instruction: 0,
        })
        .unwrap();
    let copies = reflected.function(function).unwrap().blocks[0].body.len() - 2;
    let returning = catalog
        .fetch(Coordinate {
            function,
            block,
            instruction: if wrong_return_pc { 0 } else { 1 + copies },
        })
        .unwrap();
    let Inst::Const {
        value: Constant::Int(literal),
        ..
    } = &reflected.node(function, block, 0).unwrap().inst
    else {
        panic!("literal fixture must actually contain Const");
    };
    let value = u64::try_from(*literal).unwrap();
    let candidate_value = if false_scalar_value {
        value.wrapping_add(1)
    } else {
        value
    };
    let scalar = app("IRScalar.int_", [nat(candidate_value)]);
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let arguments = list("IRScalar", &[]);
    let memory_guard = assembler
        .conversion(
            c("Bool"),
            EntryTarget::memory_admission(memory(173)),
            c("Bool.true"),
        )
        .unwrap();
    let entry_guard = assembler
        .conversion(
            c("Bool"),
            entry.admission(&model, arguments.clone()).unwrap(),
            c("Bool.true"),
        )
        .unwrap();
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            arguments,
            memory(173),
            nat(37),
            memory_guard,
            entry_guard,
        )
        .unwrap();
    let initialized_world = initialized.current().world.clone();
    assert_eq!(initialized.equality().left(), &initial(&model, function));

    let checks = constant
        .scalar_checks(&model, initialized.current(), scalar.clone())
        .unwrap();
    let evaluated = assembler
        .conversion(
            c("IRStepResult"),
            checks.evaluation,
            app("IRStepResult.value", [scalar.clone()]),
        )
        .unwrap();
    let operands = assembler
        .conversion(c("Bool"), checks.operands, c("Bool.true"))
        .unwrap();
    let result = assembler
        .conversion(c("Bool"), checks.result, c("Bool.true"))
        .unwrap();
    let mut transferred = constant
        .scalar_value(
            &mut assembler,
            &model,
            initialized.current(),
            scalar,
            ScalarPremises {
                evaluated,
                operands,
                result,
                before: initialized.valid().clone(),
            },
        )
        .unwrap();
    assert_eq!(
        transferred.current().world,
        initialized_world,
        "scalar transfer must preserve the entire world"
    );

    let mut prefix = transferred.run().clone();
    for pc in 1..=copies {
        let copying = catalog
            .fetch(Coordinate {
                function,
                block,
                instruction: pc,
            })
            .unwrap();
        let Inst::Copy { ty, operand } = &reflected.node(function, block, pc).unwrap().inst else {
            panic!("the actual reflected body must contain Copy at this coordinate");
        };
        assert_eq!(ty, &Ty::U64);
        assert_eq!(
            copying.instruction,
            app(
                "IRInst.copy",
                [
                    app("IRTy.uint_", [nat(64)]),
                    nat(u64::from(operand.index()))
                ]
            )
        );
        let scalar = app(
            "IRScalar.int_",
            [nat(if false_copy_value {
                value.wrapping_add(1)
            } else {
                value
            })],
        );
        let checks = copying
            .scalar_checks(&model, transferred.current(), scalar.clone())
            .unwrap();
        let evaluated = assembler
            .conversion(
                c("IRStepResult"),
                checks.evaluation,
                app("IRStepResult.value", [scalar.clone()]),
            )
            .unwrap();
        let operands = assembler
            .conversion(c("Bool"), checks.operands, c("Bool.true"))
            .unwrap();
        let result = assembler
            .conversion(c("Bool"), checks.result, c("Bool.true"))
            .unwrap();
        transferred = copying
            .scalar_value(
                &mut assembler,
                &model,
                transferred.current(),
                scalar,
                ScalarPremises {
                    evaluated,
                    operands,
                    result,
                    before: transferred.valid().clone(),
                },
            )
            .unwrap();
        assert_eq!(transferred.current().world, initialized_world);
        prefix = assembler
            .concatenate(prefix, transferred.run().clone())
            .unwrap();
    }

    // The public specialized ReturnTransfer resumes a caller. For this root
    // return use the existing fetched-step boundary, then a conversion of the
    // actual ir_byte_return_v1 dispatch. Final kernel replay must prove that
    // conversion, including owner retirement; Rust cannot credit it itself.
    // Keep the claimed final literal unchanged even in the false-premise
    // control: rejection must inspect the proof, not just notice a changed
    // final comparand.
    let terminal = terminal_override.unwrap_or_else(|| expected_terminal(value));
    let returned_world = terminal.get_app_args()[2].clone();
    let return_dispatch = returning
        .step(
            &mut assembler,
            &model,
            transferred.current(),
            transferred.valid().clone(),
        )
        .unwrap();
    let return_reduction = assembler
        .conversion(
            model.config_type(),
            return_dispatch.right().clone(),
            terminal,
        )
        .unwrap();
    let returned_step = assembler
        .compose(return_dispatch, return_reduction)
        .unwrap();
    let returned_run = assembler
        .one_step(&model, transferred.current().running(&model), returned_step)
        .unwrap();
    let execution = assembler.concatenate(prefix, returned_run).unwrap();

    // Transport the run across *proved initialization*, rather than beginning
    // the claim at an assumed already-running frame. Congruence endpoints are
    // beta-redexes, so make both conversion obligations explicit.
    let mapped = assembler
        .congruence(
            initialized.equality().clone(),
            model.config_type(),
            |state| model.run(execution.fuel(), state),
        )
        .unwrap();
    let before = assembler
        .conversion(
            model.config_type(),
            model.run(
                &NatTerm::literal(2 + copies as u64),
                initial(&model, function),
            ),
            mapped.left().clone(),
        )
        .unwrap();
    let after = assembler
        .conversion(
            model.config_type(),
            mapped.right().clone(),
            execution.equality().left().clone(),
        )
        .unwrap();
    let complete = assembler.compose(before, mapped).unwrap();
    let complete = assembler.compose(complete, after).unwrap();
    let complete = assembler
        .compose(complete, execution.equality().clone())
        .unwrap();
    let closed = scope.close(complete.term()).unwrap();
    assert!(
        !closed.has_fvar_quick(),
        "no fixture premise may remain free"
    );
    Candidate {
        proof_bytes: trust_ir::proof::encode_clean_expr_v1(&closed).unwrap(),
        initialized_world,
        returned_world,
    }
}

fn rejects(source: &LiteralReturn, module: &Module, bytes: &[u8]) {
    let error = checker().recheck(source, module, bytes).unwrap_err();
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
            "negative must fail semantically, not by a resource limit: {error}"
        );
    }
}

#[test]
fn actual_const_return_replays_initialization_scalar_return_and_whole_world() {
    for value in [0, 42, u64::from(u32::MAX), u64::MAX] {
        let (module, function, block) = target(value);
        let source = LiteralReturn {
            function,
            value,
            copies: 0,
        };
        let candidate = assemble(&module, function, block, None, false, false);
        let checked = checker()
            .recheck(&source, &module, &candidate.proof_bytes)
            .unwrap();
        assert!(std::ptr::eq(checked.source(), &source));
        assert!(std::ptr::eq(checked.target(), &module));
        assert_eq!(checked.proof_term(), candidate.proof_bytes);
        assert_eq!(candidate.returned_world, world(173, 37, &[], 9));
        assert_ne!(
            candidate.initialized_world, candidate.returned_world,
            "a root return must pop the activation owner, not preserve the running world"
        );
    }
}

#[test]
fn whole_claim_rejects_changed_literal_source_and_actual_target() {
    let (module, function, block) = target(42);
    let source = LiteralReturn {
        function,
        value: 42,
        copies: 0,
    };
    let candidate = assemble(&module, function, block, None, false, false);
    rejects(
        &LiteralReturn {
            value: 43,
            ..source
        },
        &module,
        &candidate.proof_bytes,
    );
    let (changed, _, _) = target(43);
    rejects(&source, &changed, &candidate.proof_bytes);
}

#[test]
fn candidates_with_false_scalar_premise_or_wrong_fetched_return_pc_do_not_replay() {
    let (module, function, block) = target(42);
    let source = LiteralReturn {
        function,
        value: 42,
        copies: 0,
    };
    for (wrong_pc, false_value) in [(true, false), (false, true)] {
        let candidate = assemble(&module, function, block, None, wrong_pc, false_value);
        rejects(&source, &module, &candidate.proof_bytes);
    }
}

#[test]
fn whole_claim_rejects_same_return_value_with_wrong_terminal_world() {
    let (module, function, block) = target(42);
    let source = LiteralReturn {
        function,
        value: 42,
        copies: 0,
    };
    for wrong_world in [
        world(174, 37, &[], 9),       // lost/changed bytes
        world(173, 38, &[], 9),       // changed provider host state
        world(173, 37, &[nat(8)], 9), // owner not retired/popped
        world(173, 37, &[], 8),       // fresh-owner cursor rewound
        world(173, 37, &[], 2),       // historical owner ignored
    ] {
        let candidate = assemble(
            &module,
            function,
            block,
            Some(halted(42, wrong_world)),
            false,
            false,
        );
        rejects(&source, &module, &candidate.proof_bytes);
    }
}

#[test]
fn value_only_proof_and_trailing_bytes_cannot_replace_whole_execution_evidence() {
    let (module, function, block) = target(42);
    let source = LiteralReturn {
        function,
        value: 42,
        copies: 0,
    };
    let value_only = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [c("IRScalar"), app("IRScalar.int_", [nat(42)])],
    );
    rejects(
        &source,
        &module,
        &trust_ir::proof::encode_clean_expr_v1(&value_only).unwrap(),
    );
    let mut candidate = assemble(&module, function, block, None, false, false);
    candidate.proof_bytes.push(0);
    assert_eq!(
        checker()
            .recheck(&source, &module, &candidate.proof_bytes)
            .unwrap_err()
            .stage(),
        "decode"
    );
}

#[test]
fn actual_copy_chains_replay_original_typed_instructions_and_complete_worlds() {
    for copies in [1, 2] {
        for value in [0, 42, u64::from(u32::MAX), u64::MAX] {
            let (module, function, block) = target_with_copies(value, copies);
            let source = LiteralReturn {
                function,
                value,
                copies,
            };
            let candidate = assemble(&module, function, block, None, false, false);
            let checked = checker()
                .recheck(&source, &module, &candidate.proof_bytes)
                .unwrap();
            assert!(std::ptr::eq(checked.target(), &module));
            assert_eq!(candidate.returned_world, world(173, 37, &[], 9));
        }
    }
}

#[test]
fn actual_copy_rejects_forged_evaluation_and_same_value_with_wrong_world() {
    let (module, function, block) = target_with_copies(42, 1);
    let source = LiteralReturn {
        function,
        value: 42,
        copies: 1,
    };
    let forged = assemble_with_copy_fault(&module, function, block, None, false, false, true);
    rejects(&source, &module, &forged.proof_bytes);
    for changed in [
        world(174, 37, &[], 9),
        world(173, 38, &[], 9),
        world(173, 37, &[nat(8)], 9),
        world(173, 37, &[], 8),
    ] {
        let forged = assemble(
            &module,
            function,
            block,
            Some(halted(42, changed)),
            false,
            false,
        );
        rejects(&source, &module, &forged.proof_bytes);
    }
}

#[test]
fn copy_reflection_requires_original_operand_type_agreement() {
    let (module, function, block) = target_with_copies(42, 1);
    for wrong_ty in [Ty::I64, Ty::Bool, Ty::Ptr] {
        let mut changed = module.clone();
        let Inst::Copy { ty, .. } = &mut changed.functions[0].blocks[0].body[1].inst else {
            unreachable!()
        };
        *ty = wrong_ty;
        assert!(reflect_core_module_v1(&changed, &[(function, 4096)]).is_err());
    }
    let source = LiteralReturn {
        function,
        value: 42,
        copies: 1,
    };
    let candidate = assemble(&module, function, block, None, false, false);
    rejects(
        &LiteralReturn {
            value: 43,
            ..source
        },
        &module,
        &candidate.proof_bytes,
    );
    let (changed, _, _) = target_with_copies(43, 1);
    rejects(&source, &changed, &candidate.proof_bytes);
}
