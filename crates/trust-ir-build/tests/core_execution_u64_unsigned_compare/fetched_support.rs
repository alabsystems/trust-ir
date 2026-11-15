// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::BinderInfo;
use trust_ir::{BlockId, Endianness, FuncId, Module, StructPassingPolicy, TargetInfo, Ty, ValueId};
use trust_ir_build::{
    ModuleBuilder,
    core_execution::{
        Catalog, Coordinate, EntryTarget, MachineModel, NatTerm, PendingEquality, RootReturnFrame,
        ScalarPremises,
    },
    core_reflection::reflect_core_module_v1,
    translation::{SourceTranslationModel, TranslationRechecker},
};

pub(super) const FUNCTION: FuncId = FuncId::new(0);
pub(super) const BLOCK: BlockId = BlockId::new(0);

pub(super) fn list(ty: &str, values: &[Expr]) -> Expr {
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
fn providers() -> Expr {
    let returned = app(
        "IRByteImportResultV1.mk",
        [
            c("Nat"),
            app("IROutcome.stuck", [c("IRFault.no_func")]),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );
    [
        c("Nat"),
        app("IRList", [c("IRScalar")]),
        c("IRByteMemoryV1"),
        c("Nat"),
    ]
    .into_iter()
    .rev()
    .fold(returned, |body, ty| lam(ty, body))
}
pub(super) fn memory(byte: u64) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list(
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
            ),
            lam(c("Nat"), app("IROption.some", [c("Nat"), nat(byte)])),
            nat(128),
        ],
    )
}
pub(super) fn world(byte: u64, host: u64, owners: &[Expr], next: u64) -> Expr {
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
pub(super) fn model(module: &Module) -> MachineModel {
    let reflected = reflect_core_module_v1(module, &[(FUNCTION, 4096)]).unwrap();
    MachineModel::new(c("Nat"), &reflected, providers())
}
pub(super) fn initial(model: &MachineModel, words: [Expr; 2]) -> Expr {
    app(
        "ir_byte_init_v1",
        [
            c("Nat"),
            model.context().clone(),
            nat(0),
            list(
                "IRScalar",
                &[scalar(words[0].clone()), scalar(words[1].clone())],
            ),
            memory(173),
            nat(37),
        ],
    )
}
pub(super) fn terminal(value: Expr, final_world: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[value])]),
            final_world,
        ],
    )
}
pub(super) fn fixture(carrier: Carrier, op: ICmpOp) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "full64_unsigned_comparison",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let ty = match carrier {
        Carrier::Unsigned => Ty::U64,
        Carrier::Signed => Ty::I64,
    };
    let signature = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![Ty::Bool]);
    assert_eq!(
        builder.declare_function("compare_words", signature),
        FUNCTION
    );
    let mut function = builder.define_function(FUNCTION).unwrap();
    let block = function.create_block();
    assert_eq!(block, BLOCK);
    let a = function.add_block_param(block, ty.clone());
    let b = function.add_block_param(block, ty.clone());
    function.switch_to_block(block);
    let compared = function.icmp(op, ty, a, b);
    assert_eq!(
        (a, b, compared),
        (ValueId::new(0), ValueId::new(1), ValueId::new(2))
    );
    function.ret(vec![compared]);
    function.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn truth(assembler: &mut Assembler<'_>, left: Expr) -> PendingEquality {
    assembler
        .conversion(c("Bool"), left, c("Bool.true"))
        .unwrap()
}
fn and(a: PendingEquality, b: PendingEquality) -> PendingEquality {
    PendingEquality::candidate(
        c("Bool"),
        app("Bool.and", [a.left().clone(), b.left().clone()]),
        c("Bool.true"),
        app(
            "ir_byte_world_and_intro_v1",
            [
                a.left().clone(),
                b.left().clone(),
                a.term().clone(),
                b.term().clone(),
            ],
        ),
    )
}
fn fit(
    model: &MachineModel,
    carrier: Carrier,
    word: Expr,
    bounded: &PendingProof,
) -> PendingEquality {
    let rule = match carrier {
        Carrier::Unsigned => "ir_byte_u64_value_fits_v1",
        Carrier::Signed => "ir_byte_i64_value_fits_v1",
    };
    let canonical = app(
        "ir_byte_ltb_of_lt_v1",
        [
            word.clone(),
            app("ir_nat_pow2", [nat(64)]),
            bounded.term().clone(),
        ],
    );
    PendingEquality::candidate(
        c("Bool"),
        app(
            "ir_byte_value_matches_v1",
            [
                model.context().clone(),
                carrier.ty(64),
                scalar(word.clone()),
            ],
        ),
        c("Bool.true"),
        app(rule, [model.context().clone(), word, canonical]),
    )
}

/// Actual entry, one fetched ICmp, then actual root Return. Only canonical
/// input bounds are supplied; entry/lookup/carrier/result/world equations are
/// separately derived. No desired Bool or terminal equality is a premise.
pub(super) fn execute(
    module: &Module,
    carrier: Carrier,
    op: ICmpOp,
    words: [Expr; 2],
    bounds: [PendingProof; 2],
    assembler: &mut Assembler<'_>,
) -> (
    MachineModel,
    PendingEquality,
    PendingEquality,
    PendingEquality,
) {
    let reflected = reflect_core_module_v1(module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(FUNCTION).unwrap();
    let arguments = list(
        "IRScalar",
        &[scalar(words[0].clone()), scalar(words[1].clone())],
    );
    let a_fit = fit(&model, carrier, words[0].clone(), &bounds[0]);
    let b_fit = fit(&model, carrier, words[1].clone(), &bounds[1]);
    let empty_fit = truth(assembler, c("Bool.true"));
    let args_fit = and(a_fit.clone(), and(b_fit.clone(), empty_fit));
    let admitted = assembler
        .convert_endpoints(
            args_fit,
            entry.admission(&model, arguments.clone()).unwrap(),
            c("Bool.true"),
        )
        .unwrap();
    let memory_guard = truth(assembler, EntryTarget::memory_admission(memory(173)));
    let initialized = entry
        .initialize(
            assembler,
            &model,
            arguments,
            memory(173),
            nat(37),
            memory_guard,
            admitted,
        )
        .unwrap();
    let original = initialized.current();
    let site = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block: BLOCK,
            instruction: 0,
        })
        .unwrap();
    assert_eq!(*site.instruction.get_app_fn(), c("IRInst.icmp"));
    assert_eq!(site.results, list("Nat", &[nat(2)]));
    let value = boolean(observer(op, words[0].clone(), words[1].clone()));
    let checks = site.scalar_checks(&model, original, value.clone()).unwrap();
    let before = assembler.operations();
    let (derived, evaluated) = carrier
        .derive(assembler, op, words.clone(), bounds)
        .unwrap();
    assert_eq!(assembler.operations(), before + 1);
    assert_eq!(derived, value);
    // The Byte dispatcher really delegates these nominal int/uint cases to
    // ir_icmp_eval. Conversion also substitutes actual looked-up operand IDs.
    let evaluated = assembler
        .convert_endpoints(evaluated, checks.evaluation, result(value.clone()))
        .unwrap();
    let operands = assembler
        .convert_endpoints(and(a_fit, b_fit), checks.operands, c("Bool.true"))
        .unwrap();
    let result_guard = truth(assembler, checks.result);
    let transfer = site
        .scalar_value(
            assembler,
            &model,
            original,
            value.clone(),
            ScalarPremises {
                evaluated,
                operands,
                result: result_guard,
                before: initialized.valid().clone(),
            },
        )
        .unwrap();
    let current = transfer.current();
    assert_eq!(current.world, original.world);
    assert_eq!(current.tail, original.tail);
    assert_eq!(current.legacy_memory, original.legacy_memory);
    assert_eq!(current.legacy_cursor, original.legacy_cursor);
    let expected_frame = app(
        "ir_frame_advance",
        [app(
            "ir_frame_set_many",
            [
                original.frame.clone(),
                list("Nat", &[nat(2)]),
                list("IRScalar", std::slice::from_ref(&value)),
            ],
        )],
    );
    assert_eq!(
        current.frame, expected_frame,
        "bind destination2 and advance PC exactly once"
    );
    assert_eq!(transfer.run().fuel().term(), &nat(1));
    let lookup = assembler
        .conversion(
            c("IRScalar"),
            app("ir_getd", [current.machine(), nat(2)]),
            value.clone(),
        )
        .unwrap();
    assert_eq!(
        transfer.run().equality().left(),
        &model.run(&NatTerm::literal(1), original.running(&model))
    );
    assert_eq!(transfer.run().equality().right(), &current.running(&model));

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
            instruction: 1,
        })
        .unwrap();
    assert_eq!(*returning.instruction.get_app_fn(), c("IRInst.ret"));
    let fields = returning.instruction.get_app_args();
    let [ids] = fields.as_slice() else {
        panic!("actual reflected Return operands")
    };
    assert_eq!(**ids, list("Nat", &[nat(2)]));
    let values = list("IRScalar", &[value]);
    let resolved = assembler
        .conversion(
            app("IRList", [c("IRScalar")]),
            app("ir_resolve", [current.machine(), (*ids).clone()]),
            values.clone(),
        )
        .unwrap();
    let target = catalog.call_target(FUNCTION).unwrap();
    let admitted = truth(
        assembler,
        returning
            .root_return_admission(&model, &target, &frame, values)
            .unwrap(),
    );
    let returned = returning
        .return_from_root(
            assembler,
            &model,
            &target,
            &frame,
            resolved,
            admitted,
            transfer.valid().clone(),
        )
        .unwrap();
    let execution = assembler
        .concatenate(transfer.run().clone(), returned.run().clone())
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
            model.run(&NatTerm::literal(2), initial(&model, words)),
            mapped.left().clone(),
        )
        .unwrap();
    let middle = assembler
        .conversion(
            model.config_type(),
            mapped.right().clone(),
            execution.equality().left().clone(),
        )
        .unwrap();
    let complete = assembler.compose(start, mapped).unwrap();
    let complete = assembler.compose(complete, middle).unwrap();
    let complete = assembler
        .compose(complete, execution.equality().clone())
        .unwrap();
    (model, complete, lookup, transfer.run().equality().clone())
}

#[derive(Clone, Copy)]
pub(super) struct Claim {
    pub carrier: Carrier,
    pub op: ICmpOp,
    pub a: u64,
    pub b: u64,
    pub answer: bool,
}
pub(super) struct WholeModel;
impl SourceTranslationModel for WholeModel {
    type Source = Claim;
    fn build_environment() -> Result<Environment, String> {
        Ok(environment().clone())
    }
    fn reconstruct(source: &Claim, target: &Module) -> Result<Expr, String> {
        if !trust_ir_build::validate_module(target).is_empty() {
            return Err("actual valid comparison target required".into());
        }
        let reflected = reflect_core_module_v1(target, &[(FUNCTION, 4096)])
            .map_err(|error| error.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        // Claim is an authored scalar-input/outcome specification, not a Rust
        // AST theorem. The actual target supplies ALL execution descriptors.
        Ok(eq(
            model.config_type(),
            model.run(
                &NatTerm::literal(2),
                initial(&model, [nat(source.a), nat(source.b)]),
            ),
            terminal(boolean(flag(source.answer)), world(173, 37, &[], 9)),
        ))
    }
}
pub(super) fn whole_checker() -> &'static TranslationRechecker<WholeModel> {
    static CHECKER: OnceLock<TranslationRechecker<WholeModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}
pub(super) fn rejects(claim: &Claim, module: &Module, bytes: &[u8]) {
    let error = whole_checker()
        .recheck_dag_v2(claim, module, bytes)
        .unwrap_err();
    assert_eq!(error.stage(), "kernel audit", "{error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
        "unknown constant",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "{error}"
        );
    }
}
