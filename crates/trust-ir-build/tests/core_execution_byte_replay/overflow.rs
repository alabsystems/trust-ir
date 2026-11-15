// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Authored, concrete checked-arithmetic invocations. These are not Rust
//! extraction, TLA+ source, panic, native execution or universal-input proofs.
//! Independent host arithmetic states both result lanes and the whole returned
//! world; real reflection/fetch/initialization/return undergo rooted replay.

use super::*;
use trust_ir::OverflowOp;
use trust_ir_build::core_execution::{Current, OverflowPremises, ValueBindingPremises};

const FUNCTION: FuncId = FuncId::new(0);
const BLOCK: BlockId = BlockId::new(0);

#[derive(Clone, Copy, Debug)]
struct Input {
    op: OverflowOp,
    signed: bool,
    a: u64,
    b: u64,
}

impl Input {
    fn ty(self) -> Ty {
        if self.signed { Ty::I64 } else { Ty::U64 }
    }

    // Host arithmetic is an independent source oracle, not a normalization or
    // call to the target's operational definitions or the candidate producer.
    fn result(self) -> (u64, bool) {
        if self.signed {
            let a = i64::from_ne_bytes(self.a.to_ne_bytes());
            let b = i64::from_ne_bytes(self.b.to_ne_bytes());
            let (value, flag) = match self.op {
                OverflowOp::AddOverflow => a.overflowing_add(b),
                OverflowOp::SubOverflow => a.overflowing_sub(b),
                OverflowOp::MulOverflow => a.overflowing_mul(b),
            };
            (u64::from_ne_bytes(value.to_ne_bytes()), flag)
        } else {
            match self.op {
                OverflowOp::AddOverflow => self.a.overflowing_add(self.b),
                OverflowOp::SubOverflow => self.a.overflowing_sub(self.b),
                OverflowOp::MulOverflow => self.a.overflowing_mul(self.b),
            }
        }
    }
}

fn scalar(value: u64) -> Expr {
    app("IRScalar.int_", [nat(value)])
}

fn boolean(value: bool) -> Expr {
    app(
        "IRScalar.bool_",
        [c(if value { "Bool.true" } else { "Bool.false" })],
    )
}

fn outcome(input: Input, terminal_world: Expr) -> Expr {
    let (value, flag) = input.result();
    outcome_lanes([scalar(value), boolean(flag)], terminal_world)
}

fn outcome_lanes(values: [Expr; 2], terminal_world: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.ret", [list("IRScalar", &values)]),
            terminal_world,
        ],
    )
}

fn initial(model: &MachineModel, input: Input) -> Expr {
    app(
        "ir_byte_init_v1",
        [
            c("Nat"),
            model.context().clone(),
            nat(0),
            list("IRScalar", &[scalar(input.a), scalar(input.b)]),
            memory(173),
            nat(37),
        ],
    )
}

struct CheckedArithmetic;

impl SourceTranslationModel for CheckedArithmetic {
    type Source = Input;

    fn build_environment() -> Result<Environment, String> {
        // Explicit opt-in, not a change to the ordinary ByteV1 vocabulary.
        // Actual checked packages retain the original arithmetic definitions.
        let mut owner =
            clean_verify::eval_ir::build_positive_division_byte_prelude_spec_v1_with_stack()
                .map_err(|error| error.to_string())?;
        owner
            .install_eval_ir_total_restoring_division_laws_v1()
            .map_err(|error| error.to_string())?;
        owner
            .install_eval_ir_integer_mul_residue_laws_v1()
            .map_err(|error| error.to_string())?;
        Ok(owner.env().clone())
    }

    fn reconstruct(input: &Input, module: &Module) -> Result<Expr, String> {
        let reflected =
            reflect_core_module_v1(module, &[(FUNCTION, 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(2), initial(&model, *input)),
            outcome(*input, world(173, 37, &[], 9)),
        ))
    }
}

fn checker() -> &'static TranslationRechecker<CheckedArithmetic> {
    static CHECKER: OnceLock<TranslationRechecker<CheckedArithmetic>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn fixture(input: Input) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "authored_checked_arithmetic",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let ty = input.ty();
    let signature = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone(), Ty::Bool]);
    let function = builder.declare_function("checked_arithmetic", signature);
    assert_eq!(function, FUNCTION);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    assert_eq!(block, BLOCK);
    let a = body.add_block_param(block, ty.clone());
    let b = body.add_block_param(block, ty.clone());
    body.switch_to_block(block);
    let (value, flag) = body.overflow(input.op, ty, a, b);
    body.ret(vec![value, flag]);
    body.build();
    let module = builder
        .build()
        .expect("authored two-result Overflow module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn truth(
    assembler: &mut Assembler<'_>,
    check: Expr,
) -> trust_ir_build::core_execution::PendingEquality {
    assembler
        .conversion(c("Bool"), check, c("Bool.true"))
        .unwrap()
}

fn assemble(input: Input, module: &Module, terminal_override: Option<Expr>) -> Vec<u8> {
    let reflected = reflect_core_module_v1(module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(FUNCTION).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block: BLOCK,
            instruction: 0,
        })
        .unwrap();
    let returning = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block: BLOCK,
            instruction: 1,
        })
        .unwrap();
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let arguments = list("IRScalar", &[scalar(input.a), scalar(input.b)]);
    let memory_guard = truth(&mut assembler, EntryTarget::memory_admission(memory(173)));
    let entry_guard = truth(
        &mut assembler,
        entry.admission(&model, arguments.clone()).unwrap(),
    );
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
    let current = initialized.current();
    let ty = app(
        if input.signed {
            "IRTy.int_"
        } else {
            "IRTy.uint_"
        },
        [nat(64)],
    );
    let left = assembler
        .conversion(
            c("IRScalar"),
            app("ir_getd", [current.machine(), nat(0)]),
            scalar(input.a),
        )
        .unwrap();
    let right = assembler
        .conversion(
            c("IRScalar"),
            app("ir_getd", [current.machine(), nat(1)]),
            scalar(input.b),
        )
        .unwrap();
    let left_fits = truth(
        &mut assembler,
        app("ir_byte_integer_fits_v1", [ty.clone(), nat(input.a)]),
    );
    let right_fits = truth(
        &mut assembler,
        app("ir_byte_integer_fits_v1", [ty.clone(), nat(input.b)]),
    );
    let result_types = truth(
        &mut assembler,
        app(
            "ir_byte_ty_list_eq_v1",
            [
                app("ir_byte_site_results_v1", [site.site.clone()]),
                list("IRTy", &[ty, c("IRTy.bool_")]),
            ],
        ),
    );
    let premises = OverflowPremises {
        left,
        right,
        left_fits,
        right_fits,
        result_types,
        before: initialized.valid().clone(),
    };
    let transferred = if input.op == OverflowOp::MulOverflow {
        site.overflow_mul_normalized(
            &mut assembler,
            &model,
            current,
            [nat(input.a), nat(input.b)],
            premises,
        )
    } else {
        site.overflow(
            &mut assembler,
            &model,
            current,
            [nat(input.a), nat(input.b)],
            premises,
        )
    }
    .unwrap();
    let result_guard = truth(
        &mut assembler,
        site.value_binding_check(&model, transferred.values())
            .unwrap(),
    );
    let binding = site
        .bind_values(
            &mut assembler,
            &model,
            current,
            transferred.values(),
            ValueBindingPremises {
                result: result_guard,
                before: initialized.valid().clone(),
            },
        )
        .unwrap();
    let bound_run = binding
        .complete_run(&mut assembler, transferred.run().clone())
        .unwrap();
    assert_eq!(bound_run.fuel().term(), NatTerm::literal(1).term());
    // Independently specified expected frame: literal two-lane values from the
    // source oracle, not copied from the candidate's computed result expression.
    let (value, flag) = input.result();
    let next = Current {
        frame: app(
            "ir_frame_advance",
            [app(
                "ir_frame_set_many",
                [
                    current.frame.clone(),
                    list("Nat", &[nat(2), nat(3)]),
                    list("IRScalar", &[scalar(value), boolean(flag)]),
                ],
            )],
        ),
        ..current.clone()
    };
    let prefix_equality = assembler
        .convert_endpoints(
            bound_run.equality().clone(),
            model.run(&NatTerm::literal(1), current.running(&model)),
            next.running(&model),
        )
        .unwrap();
    let prefix = trust_ir_build::core_execution::ExactRun::candidate(
        model.clone(),
        current.running(&model),
        next.running(&model),
        NatTerm::literal(1),
        prefix_equality,
    )
    .unwrap();
    let valid = assembler
        .convert_endpoints(binding.valid().clone(), next.valid(&model), c("Bool.true"))
        .unwrap();
    let returned = returning
        .step(&mut assembler, &model, &next, valid)
        .unwrap();
    let terminal = terminal_override.unwrap_or_else(|| outcome(input, world(173, 37, &[], 9)));
    let reduced = assembler
        .conversion(model.config_type(), returned.right().clone(), terminal)
        .unwrap();
    let step = assembler.compose(returned, reduced).unwrap();
    let run = assembler
        .one_step(&model, next.running(&model), step)
        .unwrap();
    let execution = assembler.concatenate(prefix, run).unwrap();
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
            model.run(&NatTerm::literal(2), initial(&model, input)),
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
    let proof = assembler.compose(before, mapped).unwrap();
    let proof = assembler.compose(proof, after).unwrap();
    let proof = assembler
        .compose(proof, execution.equality().clone())
        .unwrap();
    let closed = scope.close(proof.term()).unwrap();
    assert!(!closed.has_fvar_quick());
    trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap()
}

fn rejects(input: &Input, module: &Module, proof: &[u8]) {
    let error = checker().recheck_dag_v2(input, module, proof).unwrap_err();
    assert_eq!(error.stage(), "kernel audit", "{error}");
    for nonsemantic in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
        "missingdeclaration",
        "unknown constant",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(nonsemantic),
            "{error}"
        );
    }
}

#[test]
fn actual_checked_arithmetic_replays_both_lanes_and_complete_returned_world() {
    for input in [
        Input {
            op: OverflowOp::AddOverflow,
            signed: false,
            a: 0,
            b: 0,
        },
        Input {
            op: OverflowOp::AddOverflow,
            signed: false,
            a: u64::MAX,
            b: 1,
        },
        Input {
            op: OverflowOp::SubOverflow,
            signed: false,
            a: 0,
            b: 1,
        },
        Input {
            op: OverflowOp::MulOverflow,
            signed: false,
            a: u64::MAX,
            b: 2,
        },
        Input {
            op: OverflowOp::AddOverflow,
            signed: true,
            a: u64::from_ne_bytes(i64::MAX.to_ne_bytes()),
            b: 1,
        },
        Input {
            op: OverflowOp::SubOverflow,
            signed: true,
            a: 1_u64 << 63,
            b: 1,
        },
        Input {
            op: OverflowOp::MulOverflow,
            signed: true,
            a: 1_u64 << 63,
            b: u64::MAX,
        },
        Input {
            op: OverflowOp::MulOverflow,
            signed: true,
            a: u64::MAX,
            b: 2,
        },
    ] {
        eprintln!("OVERFLOW_ROOTED_CASE {input:?}");
        let module = fixture(input);
        let bytes = assemble(input, &module, None);
        let checked = checker()
            .recheck_dag_v2(&input, &module, &bytes)
            .unwrap_or_else(|error| panic!("checked arithmetic {input:?}: {error}"));
        assert!(std::ptr::eq(checked.source(), &input));
        assert!(std::ptr::eq(checked.target(), &module));
        assert_eq!(checked.proof_term(), &bytes);
    }
}

#[test]
fn checked_arithmetic_rejects_changed_actual_opcode_source_and_whole_world() {
    for input in [
        Input {
            op: OverflowOp::AddOverflow,
            signed: false,
            a: 3,
            b: 2,
        },
        Input {
            op: OverflowOp::MulOverflow,
            signed: true,
            a: 1_u64 << 63,
            b: u64::MAX,
        },
        Input {
            op: OverflowOp::MulOverflow,
            signed: false,
            a: u64::MAX,
            b: u64::MAX,
        },
    ] {
        reject_changed_endpoints(input);
    }
}

fn reject_changed_endpoints(input: Input) {
    let module = fixture(input);
    let bytes = assemble(input, &module, None);
    checker().recheck_dag_v2(&input, &module, &bytes).unwrap();
    let changed = Input {
        op: OverflowOp::SubOverflow,
        ..input
    };
    rejects(&changed, &module, &bytes);
    rejects(&input, &fixture(changed), &bytes);
    let (value, flag) = input.result();
    // Both returned lanes, and their order, belong to the reconstructed source
    // claim. A valid fetched opcode or preserved world cannot authorize a
    // changed mathematical result, overflow flag, or result-carrier order.
    for corrupt_values in [
        [scalar(value.wrapping_add(1)), boolean(flag)],
        [scalar(value), boolean(!flag)],
        [boolean(flag), scalar(value)],
    ] {
        let terminal = outcome_lanes(corrupt_values, world(173, 37, &[], 9));
        let forged = assemble(input, &module, Some(terminal));
        rejects(&input, &module, &forged);
    }
    for corrupt_world in [
        world(174, 37, &[], 9),
        world(173, 38, &[], 9),
        world(173, 37, &[nat(8)], 9),
        world(173, 37, &[], 8),
    ] {
        let forged = assemble(input, &module, Some(outcome(input, corrupt_world)));
        rejects(&input, &module, &forged);
    }
}
