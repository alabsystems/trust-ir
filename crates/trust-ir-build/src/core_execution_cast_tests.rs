// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual-module, actual-fetch, full-kernel cast replay. These tests install no
//! replacement evaluator or assumed conversion lemma. Their scope is a fetched
//! byte instruction, not source-to-native correctness or pointer provenance.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{CastOp, Endianness, Module, StructPassingPolicy, TargetInfo, Ty};

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .expect("canonical byte vocabulary")
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
}

fn check(proof: &Expr, proposition: &Expr) {
    assert!(!proof.has_fvar_quick());
    assert!(!proposition.has_fvar_quick());
    let checker = checker();
    checker
        .check_type(proposition, &Expr::sort(Level::zero()))
        .unwrap();
    checker.check_type(proof, proposition).unwrap();
    let audit = environment().audit_certification(proposition, proof);
    assert!(audit.is_certified(), "{audit:#?}");
}

fn rejects(proof: &Expr, proposition: &Expr) {
    let checker = checker();
    checker
        .check_type(proposition, &Expr::sort(Level::zero()))
        .unwrap();
    let error = checker.check_type(proof, proposition).unwrap_err();
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "{error:?}"
    );
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

fn providers() -> Expr {
    // A real total provider which must not be called by any cast.
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

fn world(byte: u64, host: u64, next: u64) -> Expr {
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
            Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(byte))),
            nat(192),
        ],
    );
    app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            memory,
            nat(host),
            list("Nat", &[nat(8)]),
            nat(next),
        ],
    )
}

fn int(value: u64) -> Expr {
    app("IRScalar.int_", [nat(value)])
}

fn pointer(value: u64) -> Expr {
    if value == 0 {
        constant("IRScalar.nullptr_")
    } else {
        app("IRScalar.ptr_", [nat(value)])
    }
}

struct Fixture {
    module: Module,
    function: FuncId,
    block: BlockId,
    operand: ValueId,
    alternate: ValueId,
    prefix: ValueId,
    result: ValueId,
}

fn fixture(op: CastOp, src: Ty, dst: Ty) -> Fixture {
    let mut builder = ModuleBuilder::new_with_target_info(
        "cast_replay",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![src.clone(), src.clone()], vec![dst.clone()]);
    let function = builder.declare_function("convert", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let operand = body.add_block_param(block, src.clone());
    let alternate = body.add_block_param(block, src.clone());
    body.switch_to_block(block);
    let prefix = body.uconst(Ty::U64, 93);
    let result = body.cast(op, src, dst, operand);
    body.ret(vec![result]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        crate::validate_module(&module).is_empty(),
        "actual valid module"
    );
    Fixture {
        module,
        function,
        block,
        operand,
        alternate,
        prefix,
        result,
    }
}

impl Fixture {
    fn coordinate(&self) -> Coordinate {
        Coordinate {
            function: self.function,
            block: self.block,
            instruction: 1,
        }
    }

    fn current(&self, input: Expr, alternate: Expr) -> Current {
        let binding = |id: ValueId, value| app("IRBinding.mk", [nat(u64::from(id.index())), value]);
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(u64::from(self.function.index())),
                    nat(u64::from(self.block.index())),
                    nat(1),
                    list(
                        "IRBinding",
                        &[
                            binding(self.prefix, int(93)),
                            binding(self.operand, input),
                            binding(self.alternate, alternate),
                        ],
                    ),
                    list("Nat", &[]),
                ],
            ),
            tail: list("IRFrame", &[]),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            world: world(173, 37, 9),
        }
    }

    fn expected(&self, before: &Current, value: Expr, pc: u64, duplicates: usize) -> Current {
        // Independent frame construction, NOT the assembler's binding/advance
        // functions. Old locals, root destinations and the whole world survive.
        let fields = before.frame.get_app_args();
        let binding = app("IRBinding.mk", [nat(u64::from(self.result.index())), value]);
        let mut locals = fields[3].clone();
        for _ in 0..duplicates {
            locals = app(
                "IRList.cons",
                [constant("IRBinding"), binding.clone(), locals],
            );
        }
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    fields[0].clone(),
                    fields[1].clone(),
                    nat(pc),
                    locals,
                    fields[4].clone(),
                ],
            ),
            ..before.clone()
        }
    }
}

fn candidate(
    site: &FetchedSite,
    model: &MachineModel,
    before: &Current,
    value: Expr,
) -> ScalarTransfer {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let checks = site.scalar_checks(model, before, value.clone()).unwrap();
    let evaluated = assembler
        .conversion(
            constant("IRStepResult"),
            checks.evaluation,
            app("IRStepResult.value", [value.clone()]),
        )
        .unwrap();
    let operands = assembler
        .conversion(constant("Bool"), checks.operands, constant("Bool.true"))
        .unwrap();
    let result = assembler
        .conversion(constant("Bool"), checks.result, constant("Bool.true"))
        .unwrap();
    let valid = assembler
        .conversion(constant("Bool"), before.valid(model), constant("Bool.true"))
        .unwrap();
    let mut transfer = site
        .scalar_value(
            &mut assembler,
            model,
            before,
            value,
            ScalarPremises {
                evaluated,
                operands,
                result,
                before: valid,
            },
        )
        .unwrap();
    drop(assembler);
    // The assembler deliberately returns open candidates. Close the complete
    // proof DAG in its original owner before this fixture drops that scope;
    // independent kernel replay below still checks every candidate premise.
    for equality in [
        &mut transfer.step,
        &mut transfer.run.equality,
        &mut transfer.valid,
    ] {
        assert!(!equality.ty.has_fvar_quick());
        assert!(!equality.left.has_fvar_quick());
        assert!(!equality.right.has_fvar_quick());
        equality.term = scope
            .close(&equality.term)
            .expect("owned cast proof closure");
    }
    transfer
}

#[test]
fn fetched_pointer_casts_replay_null_high_bit_and_entire_unchanged_world() {
    for signed in [true, false] {
        let word = if signed { Ty::I64 } else { Ty::U64 };
        for to_pointer in [true, false] {
            let f = if to_pointer {
                fixture(CastOp::IntToPtr, word.clone(), Ty::Ptr)
            } else {
                fixture(CastOp::PtrToInt, Ty::Ptr, word.clone())
            };
            let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
            let model = MachineModel::new(constant("Nat"), &reflected, providers());
            let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
            let site = catalog.fetch(f.coordinate()).unwrap();
            for value in [0, 16, 1_u64 << 63, u64::MAX] {
                let (input, output, alternate) = if to_pointer {
                    (int(value), pointer(value), int(9))
                } else {
                    (pointer(value), int(value), pointer(9))
                };
                let before = f.current(input, alternate);
                let transfer = candidate(&site, &model, &before, output.clone());
                let expected = f.expected(&before, output, 2, 1);
                check(
                    transfer.step().term(),
                    &eq(
                        &model.config_type(),
                        model.step(before.running(&model)),
                        expected.running(&model),
                    ),
                );
                check(
                    transfer.run().equality().term(),
                    &eq(
                        &model.config_type(),
                        model.run(&NatTerm::literal(1), before.running(&model)),
                        expected.running(&model),
                    ),
                );
                check(
                    transfer.valid().term(),
                    &eq(
                        &constant("Bool"),
                        expected.valid(&model),
                        constant("Bool.true"),
                    ),
                );
                assert_eq!(transfer.current().world, before.world);
                assert_eq!(transfer.current().tail, before.tail);
                assert_eq!(transfer.current().legacy_memory, before.legacy_memory);
                assert_eq!(transfer.current().legacy_cursor, before.legacy_cursor);
            }
        }
    }
    for name in [
        "ir_byte_cast_eval_v1",
        "ir_byte_exec_v1",
        "ir_byte_step_fetched_v1",
    ] {
        let name = Name::from_string(name);
        assert!(environment().axiom_deps(&name).unwrap().is_empty());
        assert!(environment().trust_marker_deps(&name).unwrap().is_empty());
    }
}

#[test]
fn fetched_integer_and_pointer_identity_casts_use_the_same_typed_transfer() {
    for (op, src, dst, input, output) in [
        (CastOp::Trunc, Ty::I64, Ty::U8, int(257), int(1)),
        (
            CastOp::Trunc,
            Ty::U8,
            Ty::Bool,
            int(3),
            app("IRScalar.bool_", [constant("Bool.true")]),
        ),
        (
            CastOp::ZExt,
            Ty::Bool,
            Ty::U64,
            app("IRScalar.bool_", [constant("Bool.true")]),
            int(1),
        ),
        (CastOp::ZExt, Ty::U8, Ty::U64, int(255), int(255)),
        (CastOp::SExt, Ty::I8, Ty::I64, int(255), int(u64::MAX)),
        (
            CastOp::Bitcast,
            Ty::I64,
            Ty::U64,
            int(u64::MAX),
            int(u64::MAX),
        ),
        (CastOp::PtrToPtr, Ty::Ptr, Ty::Ptr, pointer(0), pointer(0)),
        (
            CastOp::PtrToPtr,
            Ty::Ptr,
            Ty::Ptr,
            pointer(u64::MAX),
            pointer(u64::MAX),
        ),
    ] {
        let f = fixture(op, src, dst);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog.fetch(f.coordinate()).unwrap();
        let before = f.current(input.clone(), input);
        let transfer = candidate(&site, &model, &before, output.clone());
        check(
            transfer.step().term(),
            &eq(
                &model.config_type(),
                model.step(before.running(&model)),
                f.expected(&before, output, 2, 1).running(&model),
            ),
        );
    }
}

#[test]
fn fetched_cast_cannot_skip_or_duplicate_binding_or_advance() {
    let f = fixture(CastOp::IntToPtr, Ty::I64, Ty::Ptr);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let before = f.current(int(16), int(24));
    let transfer = candidate(&site, &model, &before, pointer(16));
    let left = model.step(before.running(&model));
    for (pc, duplicates) in [(1, 1), (3, 1), (2, 0), (2, 2)] {
        rejects(
            transfer.step().term(),
            &eq(
                &model.config_type(),
                left.clone(),
                f.expected(&before, pointer(16), pc, duplicates)
                    .running(&model),
            ),
        );
    }
    for changed_world in [world(174, 37, 9), world(173, 38, 9), world(173, 37, 10)] {
        let mut wrong = f.expected(&before, pointer(16), 2, 1);
        wrong.world = changed_world;
        rejects(
            transfer.step().term(),
            &eq(&model.config_type(), left.clone(), wrong.running(&model)),
        );
    }
}

#[test]
fn cast_scalar_checks_retain_the_exact_evaluator_and_fetched_operand() {
    let f = fixture(CastOp::IntToPtr, Ty::I64, Ty::Ptr);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let before = f.current(int(16), int(24));
    let checks = site.scalar_checks(&model, &before, pointer(16)).unwrap();
    assert_eq!(
        checks.evaluation,
        app(
            "ir_byte_cast_eval_v1",
            [
                model.context().clone(),
                constant("IRCastOp.inttoptr"),
                app("IRTy.int_", [nat(64)]),
                constant("IRTy.ptr_"),
                app(
                    "ir_getd",
                    [before.machine(), nat(u64::from(f.operand.index()))]
                ),
            ]
        )
    );
    assert_eq!(checks.operands, constant("Bool.true"));
    let false_value = candidate(&site, &model, &before, pointer(24));
    rejects(
        false_value.step().term(),
        &eq(
            &model.config_type(),
            model.step(before.running(&model)),
            f.expected(&before, pointer(16), 2, 1).running(&model),
        ),
    );

    // Mutated candidate instruction fields are NOT accepted merely because the
    // same actual Catalog node/site was copied into the candidate wrapper.
    let fields: Vec<Expr> = site
        .instruction
        .get_app_args()
        .into_iter()
        .cloned()
        .collect();
    for (field, changed) in [
        (0, constant("IRCastOp.bitcast")),
        (1, app("IRTy.int_", [nat(32)])),
        (2, app("IRTy.uint_", [nat(64)])),
        (3, nat(u64::from(f.alternate.index()))),
    ] {
        let mut changed_fields = fields.clone();
        changed_fields[field] = changed;
        let mut altered = site.clone();
        altered.instruction = app("IRInst.cast", changed_fields);
        let transfer = candidate(&altered, &model, &before, pointer(16));
        rejects(
            transfer.step().term(),
            &eq(
                &model.config_type(),
                model.step(before.running(&model)),
                f.expected(&before, pointer(16), 2, 1).running(&model),
            ),
        );
    }
    let mut changed_site = site.clone();
    let mut site_fields: Vec<Expr> = site.site.get_app_args().into_iter().cloned().collect();
    site_fields[5] = list("IRTy", &[app("IRTy.uint_", [nat(64)])]);
    changed_site.site = app("IRByteSiteV1.mk", site_fields);
    let transfer = candidate(&changed_site, &model, &before, pointer(16));
    rejects(transfer.step().term(), &transfer.step().proposition());
}

#[test]
fn cast_proof_replay_rejects_semantically_changed_actual_validated_modules() {
    let original = fixture(CastOp::SExt, Ty::I8, Ty::I64);
    let reflected = reflect_core_module_v1(&original.module, &[(original.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog.fetch(original.coordinate()).unwrap();
    let before = original.current(int(255), int(9));
    let transfer = candidate(&site, &model, &before, int(u64::MAX));
    check(transfer.step().term(), &transfer.step().proposition());

    let mut changed_operand = fixture(CastOp::SExt, Ty::I8, Ty::I64);
    let trust_ir::Inst::Cast { operand, .. } =
        &mut changed_operand.module.functions[0].blocks[0].body[1].inst
    else {
        unreachable!();
    };
    *operand = changed_operand.alternate;
    for changed in [
        fixture(CastOp::ZExt, Ty::I8, Ty::I64),
        fixture(CastOp::SExt, Ty::I16, Ty::I64),
        fixture(CastOp::SExt, Ty::I8, Ty::I32),
        changed_operand,
    ] {
        assert!(crate::validate_module(&changed.module).is_empty());
        let reflected =
            reflect_core_module_v1(&changed.module, &[(changed.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let before = changed.current(int(255), int(9));
        rejects(
            transfer.step().term(),
            &eq(
                &model.config_type(),
                model.step(before.running(&model)),
                changed
                    .expected(&before, int(u64::MAX), 2, 1)
                    .running(&model),
            ),
        );
    }
}

#[test]
fn actual_fetched_unsupported_widths_and_malformed_carriers_halt_exactly() {
    for (op, src, dst, input, output, outcome) in [
        (
            CastOp::IntToPtr,
            Ty::U32,
            Ty::Ptr,
            int(16),
            pointer(16),
            app("IROutcome.unmodelled", [constant("IRFault.width_bounded")]),
        ),
        (
            CastOp::PtrToInt,
            Ty::Ptr,
            Ty::U128,
            pointer(16),
            int(16),
            app("IROutcome.unmodelled", [constant("IRFault.width_bounded")]),
        ),
        (
            CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            pointer(16),
            pointer(16),
            app("IROutcome.type_error", [constant("IRFault.bad_field")]),
        ),
        (
            CastOp::PtrToInt,
            Ty::Ptr,
            Ty::I64,
            app("IRScalar.ptr_", [nat(0)]),
            int(0),
            app("IROutcome.type_error", [constant("IRFault.bad_field")]),
        ),
        (
            CastOp::IntToPtr,
            Ty::U64,
            Ty::Ptr,
            app("IRScalar.int_", [app("Nat.succ", [nat(u64::MAX)])]),
            pointer(1),
            app("IROutcome.type_error", [constant("IRFault.bad_field")]),
        ),
    ] {
        let f = fixture(op, src, dst);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog.fetch(f.coordinate()).unwrap();
        let before = f.current(input.clone(), input);
        let checks = site.scalar_checks(&model, &before, output.clone()).unwrap();
        let fault = app("IRStepResult.fault", [outcome.clone()]);
        check(
            &refl(&constant("IRStepResult"), fault.clone()),
            &eq(&constant("IRStepResult"), checks.evaluation, fault),
        );
        let halted = app(
            "IRByteConfigV1.halted",
            [constant("Nat"), outcome, before.world.clone()],
        );
        check(
            &refl(&model.config_type(), halted.clone()),
            &eq(
                &model.config_type(),
                model.step(before.running(&model)),
                halted,
            ),
        );
        let false_success = candidate(&site, &model, &before, output);
        rejects(
            false_success.step().term(),
            &false_success.step().proposition(),
        );
    }
}
