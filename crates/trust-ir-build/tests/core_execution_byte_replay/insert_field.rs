// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored nominal SSA updates through the original shared ByteV1 machine.
//! Whole-run conversion candidates retain both operands, the complete result
//! and terminal world. No source, native, ABI or aggregate-memory claim follows.

use super::*;
use clean_kernel::TypeChecker;
use trust_ir::{
    Block, FieldDef, FuncTy, Function, InstrNode, StructDef, StructId, StructRepr, ValueId,
};

const PAIR: StructId = StructId(149);

#[derive(Clone, Copy, Debug)]
struct Input {
    left: u64,
    right: u64,
    replacement: u64,
}

fn integer(value: u64) -> Expr {
    app("IRScalar.int_", [nat(value)])
}

fn aggregate(values: &[Expr]) -> Expr {
    app(
        "IRScalar.aggv",
        [values.iter().rev().fold(c("IRScalar.vnil"), |tail, value| {
            app("IRScalar.vcons", [value.clone(), tail])
        })],
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

fn fixture() -> Module {
    let mut module = Module::new("authored_nominal_insert_field");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module.structs.push(StructDef {
        id: PAIR,
        name: "pair".into(),
        fields: [0, 8]
            .into_iter()
            .map(|offset| FieldDef {
                name: format!("lane_{offset}"),
                ty: Ty::U64,
                offset: Some(offset),
            })
            .collect(),
        size: Some(16),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Struct(PAIR), Ty::U64],
            returns: vec![Ty::Struct(PAIR), Ty::U64, Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let mut function = Function::new(FuncId(0), "update_then_extract", signature, BlockId(0));
    let mut block = Block::new(BlockId(0));
    block.params = vec![(ValueId(0), Ty::Struct(PAIR)), (ValueId(1), Ty::U64)];
    block.body = vec![
        InstrNode::new(Inst::InsertField {
            ty: Ty::Struct(PAIR),
            aggregate: ValueId(0),
            field: 1,
            value: ValueId(1),
        })
        .with_result(ValueId(2)),
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U64,
            aggregate: ValueId(2),
            field: 0,
        })
        .with_result(ValueId(3)),
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U64,
            aggregate: ValueId(2),
            field: 1,
        })
        .with_result(ValueId(4)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(2), ValueId(3), ValueId(4)],
        }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    module
}

fn terminal(input: Input, state: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app(
                "IROutcome.ret",
                [list(
                    "IRScalar",
                    &[
                        aggregate(&[integer(input.left), integer(input.replacement)]),
                        integer(input.left),
                        integer(input.replacement),
                    ],
                )],
            ),
            state,
        ],
    )
}

struct FieldModel;
impl SourceTranslationModel for FieldModel {
    type Source = Input;

    fn build_environment() -> Result<Environment, String> {
        LiteralReturnByteModel::build_environment()
    }

    fn reconstruct(input: &Input, module: &Module) -> Result<Expr, String> {
        let reflected =
            reflect_core_module_v1(module, &[(FuncId(0), 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let initial = app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(0),
                list(
                    "IRScalar",
                    &[
                        aggregate(&[integer(input.left), integer(input.right)]),
                        integer(input.replacement),
                    ],
                ),
                memory(173),
                nat(37),
            ],
        );
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(4), initial),
            terminal(*input, world(173, 37, &[], 9)),
        ))
    }
}

fn checker() -> &'static TranslationRechecker<FieldModel> {
    static CHECKER: OnceLock<TranslationRechecker<FieldModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn proof(input: Input, state: Expr) -> Expr {
    refl(app("IRByteConfigV1", [c("Nat")]), terminal(input, state))
}

fn check_refusal(error: &str) {
    assert!(error.contains("TypeMismatch"), "{error}");
    let error = error.to_ascii_lowercase();
    for limit in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
    ] {
        assert!(!error.contains(limit), "{error}");
    }
}

#[test]
fn whole_updated_aggregate_and_sibling_replay_the_original_four_step_world() {
    let module = fixture();
    for input in [
        Input {
            left: 11,
            right: 22,
            replacement: 33,
        },
        Input {
            left: 0,
            right: u64::MAX,
            replacement: 1 << 63,
        },
        Input {
            left: u64::MAX,
            right: 0,
            replacement: 0,
        },
    ] {
        let candidate = proof(input, world(173, 37, &[], 9));
        let claim = FieldModel::reconstruct(&input, &module).unwrap();
        let mut kernel = TypeChecker::new(checker().environment());
        kernel.set_allow_unsafe(false);
        kernel.set_allow_partial(false);
        kernel.set_heartbeat_limit(5_000_000);
        kernel.set_max_cache_entries(100_000);
        kernel.check_type(&candidate, &claim).unwrap();
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&candidate).unwrap();
        let checked = checker().recheck_dag_v2(&input, &module, &bytes).unwrap();
        assert!(std::ptr::eq(checked.target(), &module));
    }
}

#[test]
fn stale_field_result_source_operand_and_terminal_world_are_refused() {
    let module = fixture();
    let input = Input {
        left: 11,
        right: 22,
        replacement: 33,
    };
    let bytes =
        trust_ir::proof::encode_clean_expr_dag_v2(&proof(input, world(173, 37, &[], 9))).unwrap();
    for changed in [
        Input { left: 12, ..input },
        Input {
            replacement: 34,
            ..input
        },
    ] {
        let error = checker()
            .recheck_dag_v2(&changed, &module, &bytes)
            .unwrap_err();
        assert_eq!(error.stage(), "kernel audit");
        check_refusal(error.reason());
    }
    for state in [
        world(174, 37, &[], 9),
        world(173, 38, &[], 9),
        world(173, 37, &[nat(8)], 9),
        world(173, 37, &[], 10),
    ] {
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&proof(input, state)).unwrap();
        let error = checker()
            .recheck_dag_v2(&input, &module, &bytes)
            .unwrap_err();
        assert_eq!(error.stage(), "kernel audit");
        check_refusal(error.reason());
    }
    let mut changed = module.clone();
    if let Inst::InsertField { field, .. } = &mut changed.functions[0].blocks[0].body[0].inst {
        *field = 0;
    }
    let error = checker()
        .recheck_dag_v2(&input, &changed, &bytes)
        .unwrap_err();
    assert_eq!(error.stage(), "kernel audit");
    check_refusal(error.reason());
    let mut changed = module;
    if let Inst::Return { values } = &mut changed.functions[0].blocks[0].body[3].inst {
        values[0] = ValueId(0);
    }
    let error = checker()
        .recheck_dag_v2(&input, &changed, &bytes)
        .unwrap_err();
    assert_eq!(error.stage(), "kernel audit");
    check_refusal(error.reason());
}

fn items(term: &Expr) -> Vec<Expr> {
    let mut cursor = term.clone();
    let mut values = Vec::new();
    while *cursor.get_app_fn() == c("IRList.cons") {
        let fields = cursor.get_app_args();
        values.push(fields[1].clone());
        let next = fields[2].clone();
        drop(fields);
        cursor = next;
    }
    assert_eq!(*cursor.get_app_fn(), c("IRList.nil"));
    values
}

fn audit(actual: Expr, expected: Expr, accepted: bool) {
    let ty = c("IRStepResult");
    let goal = eq(ty.clone(), actual, expected.clone());
    let report = checker()
        .environment()
        .audit_certification(&goal, &refl(ty, expected));
    assert_eq!(report.is_certified(), accepted, "{:?}", report.issues);
    if !accepted {
        check_refusal(&format!("{:?}", report.issues));
    }
}

#[test]
fn insertion_requires_both_original_nominal_operand_rows_and_the_complete_site() {
    let module = fixture();
    let reflected = reflect_core_module_v1(&module, &[(FuncId(0), 4096)]).unwrap();
    let context = reflected.context_term().clone();
    let site = items(context.get_app_args()[4]).remove(0);
    assert_eq!(*site.get_app_fn(), c("IRByteSiteV1.mkt"));
    let fields: Vec<_> = site.get_app_args().into_iter().cloned().collect();
    let pair = app("IRTy.struct_", [nat(u64::from(PAIR.index()))]);
    let word = app("IRTy.uint_", [nat(64)]);
    let row = |id, ty| app("IRByteOperandV1.mk", [nat(id), ty]);
    let original = vec![row(0, pair.clone()), row(1, word.clone())];
    assert_eq!(fields[2], nat(0));
    assert_eq!(items(&fields[5]), vec![pair.clone()]);
    assert_eq!(items(&fields[6]), original);
    let with = |rows: Option<Vec<Expr>>, results: Expr| {
        let mut fields = fields[..6].to_vec();
        fields[5] = results;
        match rows {
            Some(rows) => {
                fields.push(list("IRByteOperandV1", &rows));
                app("IRByteSiteV1.mkt", fields)
            }
            None => app("IRByteSiteV1.mk", fields),
        }
    };
    let insert = |site: Expr, field, aggregate: Expr, replacement: Expr| {
        app(
            "ir_byte_insert_field_v1",
            [
                context.clone(),
                site,
                pair.clone(),
                nat(0),
                aggregate,
                nat(field),
                nat(1),
                replacement,
            ],
        )
    };
    let input = aggregate(&[integer(11), integer(22)]);
    let success = app(
        "IRStepResult.value",
        [aggregate(&[integer(11), integer(33)])],
    );
    audit(
        insert(site.clone(), 1, input.clone(), integer(33)),
        success.clone(),
        true,
    );
    let bad = app(
        "IRStepResult.fault",
        [app("IROutcome.type_error", [c("IRFault.bad_field")])],
    );
    let absent = app(
        "IRStepResult.fault",
        [app("IROutcome.unmodelled", [c("IRFault.width_bounded")])],
    );
    let result = list("IRTy", std::slice::from_ref(&pair));
    let old = insert(with(None, result.clone()), 1, input.clone(), integer(33));
    audit(old.clone(), absent, true);
    audit(old, success.clone(), false);
    for rows in [
        vec![original[0].clone()],
        vec![original[1].clone()],
        vec![row(9, pair.clone()), original[1].clone()],
        vec![row(0, app("IRTy.struct_", [nat(31)])), original[1].clone()],
        vec![original[0].clone(), row(1, c("IRTy.bool_"))],
        vec![original[0].clone(), row(1, app("IRTy.uint_", [nat(32)]))],
        vec![
            original[0].clone(),
            original[0].clone(),
            original[1].clone(),
        ],
        vec![
            original[0].clone(),
            original[1].clone(),
            row(1, c("IRTy.bool_")),
        ],
    ] {
        let actual = insert(
            with(Some(rows), result.clone()),
            1,
            input.clone(),
            integer(33),
        );
        audit(actual.clone(), bad.clone(), true);
        audit(actual, success.clone(), false);
    }
    for results in [list("IRTy", &[]), list("IRTy", std::slice::from_ref(&word))] {
        let actual = insert(
            with(Some(original.clone()), results),
            1,
            input.clone(),
            integer(33),
        );
        audit(actual.clone(), bad.clone(), true);
        audit(actual, success.clone(), false);
    }
    let bounds = insert(site.clone(), 2, input.clone(), integer(33));
    audit(
        bounds.clone(),
        app(
            "IRStepResult.fault",
            [app("IROutcome.ub", [c("IRFault.bad_field")])],
        ),
        true,
    );
    audit(bounds, success.clone(), false);
    for (aggregate, replacement) in [
        (aggregate(&[integer(11)]), integer(33)),
        (input, app("IRScalar.bool_", [c("Bool.true")])),
    ] {
        let actual = insert(site.clone(), 1, aggregate, replacement);
        audit(actual.clone(), bad.clone(), true);
        audit(actual, success.clone(), false);
    }
}
