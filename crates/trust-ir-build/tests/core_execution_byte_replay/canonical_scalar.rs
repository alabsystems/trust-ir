// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary authored scalar consumer, not an extracted source/native proof.
//! The existing fetched-site APIs execute both comparisons and a Select with
//! an arbitrary Boolean input. Independently replay the original whole-world
//! claim, including initialization and genuine root Return/owner retirement.
//! No successful evaluator answer or terminal equality is an input premise.

use super::*;
use trust_ir::{ICmpOp, ValueId};
use trust_ir_build::core_execution::{PendingEquality, RootReturnFrame};

const FUNCTION: FuncId = FuncId::new(0);
const BLOCK: BlockId = BlockId::new(0);

fn scalar(word: Expr) -> Expr {
    app("IRScalar.int_", [word])
}

fn boolean(value: bool) -> Expr {
    app(
        "IRScalar.bool_",
        [c(if value { "Bool.true" } else { "Bool.false" })],
    )
}

fn selected(flag: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [lam(c("Bool"), c("Nat")), right, left, flag],
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

fn truth(assembler: &mut Assembler<'_>, term: Expr) -> PendingEquality {
    assembler
        .conversion(c("Bool"), term, c("Bool.true"))
        .unwrap()
}

fn and(left: PendingEquality, right: PendingEquality) -> PendingEquality {
    PendingEquality::candidate(
        c("Bool"),
        app("Bool.and", [left.left().clone(), right.left().clone()]),
        c("Bool.true"),
        app(
            "ir_byte_world_and_intro_v1",
            [
                left.left().clone(),
                right.left().clone(),
                left.term().clone(),
                right.term().clone(),
            ],
        ),
    )
}

#[derive(Clone, Copy)]
struct Claim {
    left: u64,
    right: u64,
    equal: bool,
    signed: bool,
}

impl Claim {
    fn ty(self) -> Ty {
        if self.signed { Ty::I64 } else { Ty::U64 }
    }

    fn arguments(self, flag: Expr) -> Expr {
        list(
            "IRScalar",
            &[
                app("IRScalar.bool_", [flag]),
                scalar(nat(self.left)),
                scalar(nat(self.right)),
            ],
        )
    }

    fn values(self, flag: Expr) -> Expr {
        list(
            "IRScalar",
            &[
                boolean(self.equal),
                boolean(!self.equal),
                scalar(selected(flag, nat(self.left), nat(self.right))),
            ],
        )
    }

    fn initial(self, model: &MachineModel, flag: Expr) -> Expr {
        app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(0),
                self.arguments(flag),
                memory(173),
                nat(37),
            ],
        )
    }

    fn terminal(self, flag: Expr, terminal_world: Expr) -> Expr {
        app(
            "IRByteConfigV1.halted",
            [
                c("Nat"),
                app("IROutcome.ret", [self.values(flag)]),
                terminal_world,
            ],
        )
    }
}

struct CanonicalScalarModel;

impl SourceTranslationModel for CanonicalScalarModel {
    type Source = Claim;

    fn build_environment() -> Result<Environment, String> {
        LiteralReturnByteModel::build_environment()
    }

    fn reconstruct(source: &Claim, target: &Module) -> Result<Expr, String> {
        let reflected = reflect_core_module_v1(target, &[(FUNCTION, 4096)])
            .map_err(|error| error.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        // This binder and endpoint are reconstructed from the source, not
        // copied from a candidate transfer or obtained by normalizing the run.
        Ok(Expr::pi(
            BinderInfo::Default,
            c("Bool"),
            eq(
                model.config_type(),
                model.run(&NatTerm::literal(4), source.initial(&model, Expr::bvar(0))),
                source.terminal(Expr::bvar(0), world(173, 37, &[], 9)),
            ),
        ))
    }
}

fn checker() -> &'static TranslationRechecker<CanonicalScalarModel> {
    static CHECKER: OnceLock<TranslationRechecker<CanonicalScalarModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn fixture(claim: Claim) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "canonical_scalar_consumer",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let ty = claim.ty();
    let signature = builder.add_func_type(
        vec![Ty::Bool, ty.clone(), ty.clone()],
        vec![Ty::Bool, Ty::Bool, ty.clone()],
    );
    let id = builder.declare_function("canonical_scalar", signature);
    assert_eq!(id, FUNCTION);
    let mut function = builder.define_function(id).unwrap();
    let block = function.create_block();
    assert_eq!(block, BLOCK);
    let flag = function.add_block_param(block, Ty::Bool);
    let left = function.add_block_param(block, ty.clone());
    let right = function.add_block_param(block, ty.clone());
    function.switch_to_block(block);
    let equal = function.icmp(ICmpOp::Eq, ty.clone(), left, right);
    let unequal = function.icmp(ICmpOp::Ne, ty.clone(), left, right);
    let choice = function.select(ty, flag, left, right);
    assert_eq!(
        (flag, left, right, equal, unequal, choice),
        (
            ValueId::new(0),
            ValueId::new(1),
            ValueId::new(2),
            ValueId::new(3),
            ValueId::new(4),
            ValueId::new(5),
        )
    );
    function.ret(vec![equal, unequal, choice]);
    function.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Fault {
    None,
    EqAnswer,
    NeAnswer,
    EqOperand,
    SelectCondition,
    SelectArms,
    Carrier,
    Destination,
    Site,
    Pc,
}

fn assemble(module: &Module, claim: Claim, fault: Fault, terminal_world: Option<Expr>) -> Vec<u8> {
    let reflected = reflect_core_module_v1(module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(FUNCTION).unwrap();
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let flag = assembler.local(c("Bool")).unwrap();
    let arguments = claim.arguments(flag.term().clone());
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
    let original = initialized.current().clone();
    let mut current = original.clone();
    let mut valid = initialized.valid().clone();
    let mut prefix = assembler.zero(&model, current.running(&model)).unwrap();
    let ty = app(
        if claim.signed {
            "IRTy.int_"
        } else {
            "IRTy.uint_"
        },
        [nat(64)],
    );
    let fit_name = if claim.signed {
        "ir_byte_i64_value_fits_v1"
    } else {
        "ir_byte_u64_value_fits_v1"
    };
    let mut selected_fit = None;
    for pc in 0..3 {
        let mut site = catalog
            .fetch(Coordinate {
                function: FUNCTION,
                block: BLOCK,
                instruction: if pc == 2 && fault == Fault::Pc { 1 } else { pc },
            })
            .unwrap();
        if pc == 2 && fault == Fault::Destination {
            site.results = list("Nat", &[nat(97)]);
        }
        if pc == 2 && fault == Fault::Site {
            let mut fields: Vec<Expr> = site.site.get_app_args().into_iter().cloned().collect();
            fields[5] = list("IRTy", &[app("IRTy.usize_", [nat(64)])]);
            site.site = app("IRByteSiteV1.mk", fields);
        }
        let (value, evaluated_proof, fits) = if pc < 2 {
            let answer = if pc == 0 {
                claim.equal ^ (fault == Fault::EqAnswer)
            } else {
                !claim.equal ^ (fault == Fault::NeAnswer)
            };
            let value = boolean(answer);
            let proof = app(
                &format!(
                    "ir_byte_icmp_{}_{}_canonical_v1",
                    if claim.signed { "int" } else { "uint" },
                    if pc == 0 { "eq" } else { "ne" }
                ),
                [
                    nat(64),
                    nat(claim.left),
                    nat(if pc == 0 && fault == Fault::EqOperand {
                        claim.left
                    } else {
                        claim.right
                    }),
                    refl(c("Bool"), c("Bool.true")),
                    refl(c("Bool"), c("Bool.true")),
                ],
            );
            let fits = truth(
                &mut assembler,
                app(
                    "ir_byte_value_matches_v1",
                    [model.context().clone(), c("IRTy.bool_"), value.clone()],
                ),
            );
            (value, proof, fits)
        } else {
            let selecting_flag = if fault == Fault::SelectCondition {
                app("Bool.not", [flag.term().clone()])
            } else {
                flag.term().clone()
            };
            let (left, right) = if fault == Fault::SelectArms {
                (nat(claim.right), nat(claim.left))
            } else {
                (nat(claim.left), nat(claim.right))
            };
            let word = selected(selecting_flag.clone(), left.clone(), right.clone());
            let value = if fault == Fault::Carrier {
                boolean(true)
            } else {
                scalar(word.clone())
            };
            let evaluated = app(
                "ir_byte_select_word_eval_v1",
                [selecting_flag.clone(), left.clone(), right.clone()],
            );
            let canonical = app(
                "ir_byte_select_word_bound_v1",
                [
                    nat(64),
                    selecting_flag,
                    left,
                    right,
                    refl(c("Bool"), c("Bool.true")),
                    refl(c("Bool"), c("Bool.true")),
                ],
            );
            let fits = PendingEquality::candidate(
                c("Bool"),
                app(
                    "ir_byte_value_matches_v1",
                    [model.context().clone(), ty.clone(), value.clone()],
                ),
                c("Bool.true"),
                app(fit_name, [model.context().clone(), word, canonical]),
            );
            selected_fit = Some(fits.clone());
            (value, evaluated, fits)
        };
        let checks = site.scalar_checks(&model, &current, value.clone()).unwrap();
        let evaluated = PendingEquality::candidate(
            c("IRStepResult"),
            checks.evaluation,
            app("IRStepResult.value", [value.clone()]),
            evaluated_proof,
        );
        let operands = truth(&mut assembler, checks.operands);
        let arity = truth(&mut assembler, c("Bool.true"));
        let tail = truth(&mut assembler, c("Bool.true"));
        let result_proof = and(arity, and(fits, tail));
        let result = PendingEquality::candidate(
            c("Bool"),
            checks.result,
            c("Bool.true"),
            result_proof.term().clone(),
        );
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
                    before: valid,
                },
            )
            .unwrap();
        assert_eq!(transferred.current().world, original.world);
        assert_eq!(transferred.current().tail, original.tail);
        assert_eq!(transferred.current().legacy_memory, original.legacy_memory);
        assert_eq!(transferred.current().legacy_cursor, original.legacy_cursor);
        prefix = assembler
            .concatenate(prefix, transferred.run().clone())
            .unwrap();
        current = transferred.current().clone();
        valid = transferred.valid().clone();
    }
    let owner = app("ir_byte_fresh_owner_v1", [memory(173)]);
    let frame = RootReturnFrame {
        returning: current.frame.clone(),
        legacy_memory: current.legacy_memory.clone(),
        legacy_cursor: current.legacy_cursor.clone(),
        memory: memory(173),
        host: nat(37),
        owner: owner.clone(),
        next: app("Nat.succ", [owner]),
    };
    assert_eq!(
        frame.current(&model).running(&model),
        current.running(&model)
    );
    let returning = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block: BLOCK,
            instruction: 3,
        })
        .unwrap();
    let target = catalog.call_target(FUNCTION).unwrap();
    assert_eq!(*returning.instruction.get_app_fn(), c("IRInst.ret"));
    let return_fields = returning.instruction.get_app_args();
    let [arguments] = return_fields.as_slice() else {
        panic!("fixture must fetch the actual Return operands");
    };
    let arguments = (*arguments).clone();
    let values = claim.values(flag.term().clone());
    let resolved = assembler
        .conversion(
            app("IRList", [c("IRScalar")]),
            app("ir_resolve", [current.machine(), arguments]),
            values.clone(),
        )
        .unwrap();
    let list_fits = and(
        truth(&mut assembler, c("Bool.true")),
        and(
            truth(&mut assembler, c("Bool.true")),
            and(selected_fit.unwrap(), truth(&mut assembler, c("Bool.true"))),
        ),
    );
    let admitted_proof = and(list_fits, truth(&mut assembler, c("Bool.true")));
    let admitted = PendingEquality::candidate(
        c("Bool"),
        returning
            .root_return_admission(&model, &target, &frame, values)
            .unwrap(),
        c("Bool.true"),
        admitted_proof.term().clone(),
    );
    let returned = returning
        .return_from_root(
            &mut assembler,
            &model,
            &target,
            &frame,
            resolved,
            admitted,
            valid,
        )
        .unwrap();
    let execution = assembler
        .concatenate(prefix, returned.run().clone())
        .unwrap();
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
            model.run(
                &NatTerm::literal(4),
                claim.initial(&model, flag.term().clone()),
            ),
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
    let complete = assembler.compose(start, mapped).unwrap();
    let complete = assembler.compose(complete, end).unwrap();
    let complete = assembler
        .compose(complete, execution.equality().clone())
        .unwrap();
    let terminal = claim.terminal(
        flag.term().clone(),
        terminal_world.unwrap_or_else(|| world(173, 37, &[], 9)),
    );
    let endpoint = assembler
        .conversion(model.config_type(), complete.right().clone(), terminal)
        .unwrap();
    let complete = assembler.compose(complete, endpoint).unwrap();
    let closed = scope.close(&flag.lam(complete.term().clone())).unwrap();
    assert!(
        !closed.has_fvar_quick(),
        "no free evaluation or post-world premise"
    );
    trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap()
}

fn rejects(claim: &Claim, module: &Module, proof: &[u8]) {
    let error = checker().recheck_dag_v2(claim, module, proof).unwrap_err();
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
            "{error}"
        );
    }
}

#[test]
fn nonzero_eq_ne_and_symbolic_select_replay_fetched_whole_world() {
    for signed in [false, true] {
        for (left, right, equal) in [(41, 41, true), (41, 53, false)] {
            let claim = Claim {
                left,
                right,
                equal,
                signed,
            };
            let module = fixture(claim);
            let original = module.clone();
            let proof = assemble(&module, claim, Fault::None, None);
            checker().recheck_dag_v2(&claim, &module, &proof).unwrap();
            assert_eq!(
                module, original,
                "proof construction must not rewrite the target"
            );
        }
    }
    for name in [
        "ir_byte_icmp_uint_eq_canonical_v1",
        "ir_byte_icmp_uint_ne_canonical_v1",
        "ir_byte_icmp_int_eq_canonical_v1",
        "ir_byte_icmp_int_ne_canonical_v1",
        "ir_byte_select_word_eval_v1",
        "ir_byte_select_word_bound_v1",
        "ir_byte_u64_value_fits_v1",
        "ir_byte_i64_value_fits_v1",
    ] {
        let name = Name::from_string(name);
        assert!(
            checker()
                .environment()
                .axiom_deps(&name)
                .unwrap()
                .is_empty()
        );
        assert!(
            checker()
                .environment()
                .trust_marker_deps(&name)
                .unwrap()
                .is_empty()
        );
    }
}

#[test]
fn canonical_scalar_candidates_keep_actual_operands_result_site_pc_and_world() {
    let claim = Claim {
        left: 41,
        right: 53,
        equal: false,
        signed: false,
    };
    let module = fixture(claim);
    for fault in [
        Fault::EqAnswer,
        Fault::NeAnswer,
        Fault::EqOperand,
        Fault::SelectCondition,
        Fault::SelectArms,
        Fault::Carrier,
        Fault::Destination,
        Fault::Site,
        Fault::Pc,
    ] {
        rejects(&claim, &module, &assemble(&module, claim, fault, None));
    }
    for terminal_world in [
        world(174, 37, &[], 9),
        world(173, 38, &[], 9),
        world(173, 37, &[nat(8)], 9),
        world(173, 37, &[], 10),
    ] {
        rejects(
            &claim,
            &module,
            &assemble(&module, claim, Fault::None, Some(terminal_world)),
        );
    }
}

#[test]
fn canonical_scalar_replay_binds_source_live_operands_opcode_select_and_return() {
    let claim = Claim {
        left: 41,
        right: 53,
        equal: false,
        signed: false,
    };
    let module = fixture(claim);
    let proof = assemble(&module, claim, Fault::None, None);
    for changed in [
        Claim { left: 53, ..claim },
        Claim { right: 41, ..claim },
        Claim {
            equal: true,
            ..claim
        },
    ] {
        rejects(&changed, &module, &proof);
    }
    for mode in 0..6 {
        let mut changed = module.clone();
        match mode {
            0 | 1 => {
                let Inst::ICmp { lhs, rhs, op, .. } =
                    &mut changed.functions[0].blocks[0].body[0].inst
                else {
                    unreachable!()
                };
                if mode == 0 {
                    *rhs = *lhs;
                } else {
                    *op = ICmpOp::Ne;
                }
            }
            2 | 3 => {
                let Inst::Select {
                    cond,
                    then_val,
                    else_val,
                    ..
                } = &mut changed.functions[0].blocks[0].body[2].inst
                else {
                    unreachable!()
                };
                if mode == 2 {
                    std::mem::swap(then_val, else_val);
                } else {
                    *cond = ValueId::new(3);
                }
            }
            4 | 5 => {
                let Inst::Return { values } = &mut changed.functions[0].blocks[0].body[3].inst
                else {
                    unreachable!()
                };
                if mode == 4 {
                    values.swap(0, 1);
                } else {
                    values[2] = ValueId::new(1);
                }
            }
            _ => unreachable!(),
        }
        assert!(
            trust_ir_build::validate_module(&changed).is_empty(),
            "control must remain an admitted actual module"
        );
        rejects(&claim, &changed, &proof);
    }
}
