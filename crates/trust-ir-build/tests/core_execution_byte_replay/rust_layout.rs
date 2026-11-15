// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored NativeC SSA fixtures retaining repr(Rust) layout descriptors.
//! No actual compiler module is relabeled and no Rust ABI/source claim follows.
//! Refl below is a kernel conversion candidate, never an assumed evaluation.

use super::*;
use trust_ir::{
    Block, FieldDef, FuncTy, Function, InstrNode, StructDef, StructId, StructRepr, ValueId,
};
use trust_ir_build::core_execution::ScalarTransfer;

const ARC: StructId = StructId(149);
const EMPTY: StructId = StructId(17);
const NESTED: StructId = StructId(31);

fn pointer(address: u64) -> Expr {
    app("IRScalar.ptr_", [nat(address)])
}
fn aggregate(fields: &[Expr]) -> Expr {
    app(
        "IRScalar.aggv",
        [fields.iter().rev().fold(c("IRScalar.vnil"), |tail, field| {
            app("IRScalar.vcons", [field.clone(), tail])
        })],
    )
}
fn value(address: u64) -> Expr {
    aggregate(&[
        pointer(address),
        aggregate(&[aggregate(&[])]),
        aggregate(&[]),
    ])
}
fn refl(ty: Expr, term: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, term],
    )
}
fn fixture() -> Module {
    let mut module = Module::new("authored_native_c_rust_layout_values");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    for (id, size, align, fields) in [
        (EMPTY, 0, 1, vec![]),
        (NESTED, 0, 1, vec![(Ty::Struct(EMPTY), 0)]),
        (
            ARC,
            8,
            8,
            vec![
                (Ty::Ptr, 0),
                (Ty::Struct(NESTED), 8),
                (Ty::Struct(EMPTY), 8),
            ],
        ),
    ] {
        module.structs.push(StructDef {
            id,
            name: format!("shape_{}", id.index()),
            fields: fields
                .into_iter()
                .map(|(ty, offset)| FieldDef {
                    name: "field".into(),
                    ty,
                    offset: Some(offset),
                })
                .collect(),
            size: Some(size),
            align: Some(align),
            repr: StructRepr::Rust,
            origin: None,
        });
    }
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Struct(ARC)],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId(0), "copy_then_extract", signature, BlockId(0));
    let mut block = Block::new(BlockId(0));
    block.params.push((ValueId(0), Ty::Struct(ARC)));
    block.body = vec![
        InstrNode::new(Inst::Copy {
            ty: Ty::Struct(ARC),
            operand: ValueId(0),
        })
        .with_result(ValueId(1)),
        InstrNode::new(Inst::ExtractField {
            ty: Ty::Ptr,
            aggregate: ValueId(1),
            field: 0,
        })
        .with_result(ValueId(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(2)],
        }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    module
}
fn terminal(address: u64, state: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[pointer(address)])]),
            state,
        ],
    )
}
struct LayoutModel;
impl SourceTranslationModel for LayoutModel {
    type Source = u64;
    fn build_environment() -> Result<Environment, String> {
        LiteralReturnByteModel::build_environment()
    }
    fn reconstruct(address: &u64, module: &Module) -> Result<Expr, String> {
        let reflected =
            reflect_core_module_v1(module, &[(FuncId(0), 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(3), initial_state(&model, *address)),
            terminal(*address, world(173, 37, &[], 9)),
        ))
    }
}
fn initial_state(model: &MachineModel, address: u64) -> Expr {
    app(
        "ir_byte_init_v1",
        [
            c("Nat"),
            model.context().clone(),
            nat(0),
            list("IRScalar", &[value(address)]),
            memory(173),
            nat(37),
        ],
    )
}
fn checker() -> &'static TranslationRechecker<LayoutModel> {
    static CHECKER: OnceLock<TranslationRechecker<LayoutModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}
fn proof(address: u64, state: Expr) -> Vec<u8> {
    trust_ir::proof::encode_clean_expr_dag_v2(&refl(
        app("IRByteConfigV1", [c("Nat")]),
        terminal(address, state),
    ))
    .unwrap()
}
fn audit(ty: Expr, actual: Expr, expected: Expr, accepted: bool) {
    let goal = eq(ty.clone(), actual, expected.clone());
    let report = checker()
        .environment()
        .audit_certification(&goal, &refl(ty, expected));
    assert_eq!(report.issues.is_empty(), accepted, "{:?}", report.issues);
    if !accepted {
        let detail = format!("{:?}", report.issues).to_ascii_lowercase();
        assert!(detail.contains("typemismatch"), "{detail}");
        for resource in [
            "heartbeat",
            "budget",
            "timeout",
            "fuel exhausted",
            "recursion limit",
        ] {
            assert!(!detail.contains(resource), "{detail}");
        }
    }
}

#[test]
fn authored_rust_struct_copy_extract_replays_actual_three_step_whole_world() {
    let module = fixture();
    let original = module.clone();
    for address in [16, 24] {
        let bytes = proof(address, world(173, 37, &[], 9));
        let checked = checker().recheck_dag_v2(&address, &module, &bytes).unwrap();
        assert!(std::ptr::eq(checked.target(), &module));
    }
    assert_eq!(module, original);
    for (address, state) in [
        (24, world(173, 37, &[], 9)),
        (16, world(174, 37, &[], 9)),
        (16, world(173, 38, &[], 9)),
        (16, world(173, 37, &[nat(8)], 9)),
    ] {
        let bytes = proof(address, state);
        let error = checker().recheck_dag_v2(&16, &module, &bytes).unwrap_err();
        assert_eq!(error.stage(), "kernel audit");
        assert!(error.reason().contains("TypeMismatch"), "{error}");
    }
    let mut unclassified = module;
    unclassified.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::Unclassified;
    assert!(
        reflect_core_module_v1(&unclassified, &[(FuncId(0), 4096)])
            .unwrap_err()
            .to_string()
            .contains("scalar/thin-pointer")
    );
}

#[test]
fn nested_empty_struct_values_are_not_erased_to_unit_or_missing_fields() {
    let module = fixture();
    let reflected = reflect_core_module_v1(&module, &[(FuncId(0), 4096)]).unwrap();
    let ty = app("IRTy.struct_", [nat(149)]);
    let expected = app(
        "IRStepResult.fault",
        [app("IROutcome.type_error", [c("IRFault.bad_field")])],
    );
    for wrong in [
        aggregate(&[pointer(16), c("IRScalar.unit_"), aggregate(&[])]),
        aggregate(&[pointer(16), aggregate(&[]), aggregate(&[])]),
        aggregate(&[pointer(16), aggregate(&[aggregate(&[])])]),
        aggregate(&[
            pointer(16),
            aggregate(&[aggregate(&[])]),
            c("IRScalar.unit_"),
        ]),
    ] {
        audit(
            c("IRStepResult"),
            app(
                "ir_byte_copy_eval_v1",
                [reflected.context_term().clone(), ty.clone(), wrong],
            ),
            expected.clone(),
            true,
        );
    }
    audit(
        c("IRStepResult"),
        app("ir_ef_at", [value(16), nat(0)]),
        app("IRStepResult.value", [pointer(16)]),
        true,
    );
    audit(
        c("IRStepResult"),
        app("ir_ef_at", [value(16), nat(1)]),
        app("IRStepResult.value", [aggregate(&[aggregate(&[])])]),
        true,
    );
    audit(
        c("IRStepResult"),
        app("ir_ef_at", [value(16), nat(1)]),
        app("IRStepResult.value", [pointer(16)]),
        false,
    );
}

fn items(term: &Expr) -> Vec<Expr> {
    let mut cursor = term.clone();
    let mut out = Vec::new();
    while *cursor.get_app_fn() == c("IRList.cons") {
        let next = {
            let fields = cursor.get_app_args();
            out.push(fields[1].clone());
            fields[2].clone()
        };
        cursor = next;
    }
    assert_eq!(*cursor.get_app_fn(), c("IRList.nil"));
    out
}

/// Clean `ee4dff170` evaluates ByteV1 ExtractField with the aggregate's
/// NOMINAL type from the site's operand catalog. The reflected site carries
/// the actual operand and its actual type, so the lane is read; the SAME site
/// without a catalog (the old `mk` constructor, which this reflector emitted
/// for every site until the Clean 1d57f445 pin) halts `unmodelled`, and a
/// catalog naming another struct or another operand is a nominal type error.
/// Refl is only a kernel conversion candidate for each claimed endpoint.
#[test]
fn extract_field_reads_the_reflected_operand_catalog_not_an_absent_or_forged_one() {
    let module = fixture();
    let reflected = reflect_core_module_v1(&module, &[(FuncId(0), 4096)]).unwrap();
    let ctx = reflected.context_term().clone();
    let sites = items(ctx.get_app_args()[4]);
    let site = sites
        .iter()
        .find(|site| *site.get_app_fn() == c("IRByteSiteV1.mkt"))
        .expect("the ExtractField site carries its operand catalog")
        .clone();
    assert_eq!(
        sites
            .iter()
            .filter(|site| *site.get_app_fn() == c("IRByteSiteV1.mkt"))
            .count(),
        1
    );
    let fields: Vec<Expr> = site.get_app_args().into_iter().cloned().collect();
    assert_eq!(fields.len(), 7);
    assert_eq!(fields[2], nat(1), "the ExtractField pc");
    let lane = items(&fields[5]);
    assert_eq!(lane.len(), 1);
    let field_ty = lane[0].clone();
    let catalog = |id: u64, ty: Expr| {
        list(
            "IRByteOperandV1",
            &[app("IRByteOperandV1.mk", [nat(id), ty])],
        )
    };
    assert_eq!(fields[6], catalog(1, app("IRTy.struct_", [nat(149)])));
    let with = |operands: Option<Expr>| match operands {
        Some(operands) => app(
            "IRByteSiteV1.mkt",
            fields[..6].iter().cloned().chain([operands]),
        ),
        None => app("IRByteSiteV1.mk", fields[..6].iter().cloned()),
    };
    let extract = |site: Expr, address: u64| {
        app(
            "ir_byte_extract_field_v1",
            [
                ctx.clone(),
                site,
                field_ty.clone(),
                nat(1),
                value(address),
                nat(0),
            ],
        )
    };
    let read = |address| app("IRStepResult.value", [pointer(address)]);
    let bad = app(
        "IRStepResult.fault",
        [app("IROutcome.type_error", [c("IRFault.bad_field")])],
    );
    let absent = app(
        "IRStepResult.fault",
        [app("IROutcome.unmodelled", [c("IRFault.width_bounded")])],
    );
    let ty = c("IRStepResult");
    for address in [16, 24] {
        audit(
            ty.clone(),
            extract(site.clone(), address),
            read(address),
            true,
        );
    }
    audit(ty.clone(), extract(site.clone(), 16), read(24), false);
    audit(ty.clone(), extract(site.clone(), 16), absent.clone(), false);
    audit(ty.clone(), extract(with(None), 16), absent, true);
    audit(ty.clone(), extract(with(None), 16), read(16), false);
    for forged in [
        catalog(1, app("IRTy.struct_", [nat(31)])),
        catalog(0, app("IRTy.struct_", [nat(149)])),
        list("IRByteOperandV1", &[]),
    ] {
        let forged = with(Some(forged));
        audit(ty.clone(), extract(forged.clone(), 16), bad.clone(), true);
        audit(ty.clone(), extract(forged, 16), read(16), false);
    }
}

/// An ASSEMBLED whole-run candidate (not Refl): proved entry initialization,
/// the scalar assembler's Copy and ExtractField transfers, and the root
/// return. `extracted` is the value the ExtractField premise claims; each
/// transfer's evaluation premise is a kernel conversion obligation.
fn assembled(module: &Module, address: u64, extracted: Expr) -> Vec<u8> {
    let function = FuncId(0);
    let block = BlockId(0);
    let reflected = reflect_core_module_v1(module, &[(function, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(function).unwrap();
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let arguments = list("IRScalar", &[value(address)]);
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
    assert_eq!(
        initialized.equality().left(),
        &initial_state(&model, address)
    );
    let mut prefix = None;
    let mut transferred: Option<ScalarTransfer> = None;
    for (pc, scalar) in [(0, value(address)), (1, extracted)] {
        let site = catalog
            .fetch(Coordinate {
                function,
                block,
                instruction: pc,
            })
            .unwrap();
        let (current, before) = match &transferred {
            None => (initialized.current(), initialized.valid().clone()),
            Some(previous) => (previous.current(), previous.valid().clone()),
        };
        let checks = site.scalar_checks(&model, current, scalar.clone()).unwrap();
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
        let next = site
            .scalar_value(
                &mut assembler,
                &model,
                current,
                scalar,
                ScalarPremises {
                    evaluated,
                    operands,
                    result,
                    before,
                },
            )
            .unwrap();
        prefix = Some(match prefix {
            None => next.run().clone(),
            Some(run) => assembler.concatenate(run, next.run().clone()).unwrap(),
        });
        transferred = Some(next);
    }
    let transferred = transferred.unwrap();
    let returning = catalog
        .fetch(Coordinate {
            function,
            block,
            instruction: 2,
        })
        .unwrap();
    let dispatch = returning
        .step(
            &mut assembler,
            &model,
            transferred.current(),
            transferred.valid().clone(),
        )
        .unwrap();
    let reduction = assembler
        .conversion(
            model.config_type(),
            dispatch.right().clone(),
            terminal(address, world(173, 37, &[], 9)),
        )
        .unwrap();
    let step = assembler.compose(dispatch, reduction).unwrap();
    let returned = assembler
        .one_step(&model, transferred.current().running(&model), step)
        .unwrap();
    let execution = assembler.concatenate(prefix.unwrap(), returned).unwrap();
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
            model.run(&NatTerm::literal(3), initial_state(&model, address)),
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
    assert!(!closed.has_fvar_quick(), "no premise may remain free");
    trust_ir::proof::encode_clean_expr_v1(&closed).unwrap()
}

/// The scalar assembler's ExtractField transfer, kernel-replayed end to end.
/// Clean `ee4dff170` reads the lane through the site's operand catalog, so
/// this replays only over the reflected `mkt` site: over the old catalog-less
/// site the dispatcher halts `unmodelled` and neither the transfer's
/// evaluation premise nor its step conversion holds. (Over these CONCRETE
/// states the legacy `ir_ef_at` arm also converts, by evaluation; the arm is
/// the dispatcher's own evaluator so a premise about it composes in general.)
/// A transfer claiming another lane's value is refused by the kernel.
#[test]
fn assembled_extract_field_transfer_replays_the_nominal_evaluator() {
    let module = fixture();
    for address in [16, 24] {
        let bytes = assembled(&module, address, pointer(address));
        let checked = checker().recheck(&address, &module, &bytes).unwrap();
        assert!(std::ptr::eq(checked.target(), &module));
    }
    for forged in [pointer(24), aggregate(&[aggregate(&[])])] {
        let bytes = assembled(&module, 16, forged);
        let error = checker().recheck(&16, &module, &bytes).unwrap_err();
        assert_eq!(error.stage(), "kernel audit", "{error}");
        assert!(error.reason().contains("TypeMismatch"), "{error}");
    }
}

#[test]
fn actual_rust_descriptor_drives_allocation_extent_alignment_and_gep_stride() {
    let module = fixture();
    let reflected = reflect_core_module_v1(&module, &[(FuncId(0), 4096)]).unwrap();
    let ctx = reflected.context_term().clone();
    let ty = app("IRTy.struct_", [nat(149)]);
    let mem = memory(173);
    let fields = mem.get_app_args();
    let allocated = app(
        "IRByteMemoryV1.mk",
        [
            app(
                "IRList.cons",
                [
                    c("IRByteAllocationV1"),
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(128), nat(8), nat(8), c("Bool.true")],
                    ),
                    fields[0].clone(),
                ],
            ),
            app("ir_byte_clear_v1", [fields[1].clone(), nat(128), nat(8)]),
            nat(137),
        ],
    );
    let allocation = app(
        "ir_byte_alloc_v1",
        [ctx.clone(), ty.clone(), nat(1), nat(0), nat(8), mem.clone()],
    );
    let expected = app("IRByteMemoryResultV1.value", [pointer(128), allocated]);
    audit(
        c("IRByteMemoryResultV1"),
        allocation,
        expected.clone(),
        true,
    );
    // GEP is whole-pointee stride, not LLVM struct-field traversal.
    let gep = app(
        "ir_byte_gep_v1",
        [
            ctx,
            ty.clone(),
            pointer(16),
            list("IRScalar", &[app("IRScalar.int_", [nat(1)])]),
            c("Bool.false"),
            mem.clone(),
        ],
    );
    audit(
        c("IRByteMemoryResultV1"),
        gep.clone(),
        app("IRByteMemoryResultV1.value", [pointer(24), mem.clone()]),
        true,
    );
    audit(
        c("IRByteMemoryResultV1"),
        gep,
        app("IRByteMemoryResultV1.value", [pointer(32), mem.clone()]),
        false,
    );
    let mut changed = module;
    changed.structs[2].size = Some(16); // coherent extra padding changes allocation and stride
    let other = reflect_core_module_v1(&changed, &[(FuncId(0), 4096)]).unwrap();
    audit(
        c("IRByteMemoryResultV1"),
        app(
            "ir_byte_alloc_v1",
            [
                other.context_term().clone(),
                ty.clone(),
                nat(1),
                nat(0),
                nat(8),
                mem.clone(),
            ],
        ),
        expected,
        false,
    );
    changed.structs[2].size = Some(32);
    changed.structs[2].align = Some(32); // 128 aligned, so use a deliberately unaligned cursor
    let other = reflect_core_module_v1(&changed, &[(FuncId(0), 4096)]).unwrap();
    let empty = app("ir_byte_memory_empty_v1", [nat(129)]);
    let expected_memory = app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[app(
                    "IRByteAllocationV1.mk",
                    [nat(160), nat(32), nat(8), c("Bool.true")],
                )],
            ),
            app(
                "ir_byte_clear_v1",
                [
                    app("ir_byte_mem_bytes_v1", [empty.clone()]),
                    nat(160),
                    nat(32),
                ],
            ),
            nat(193),
        ],
    );
    audit(
        c("IRByteMemoryResultV1"),
        app(
            "ir_byte_alloc_v1",
            [
                other.context_term().clone(),
                ty,
                nat(1),
                nat(0),
                nat(8),
                empty,
            ],
        ),
        app(
            "IRByteMemoryResultV1.value",
            [pointer(160), expected_memory],
        ),
        true,
    );
}
