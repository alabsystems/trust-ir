// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual decoded-module execution, separate from observation-graph grammar.
//! Reification remains outside the general lowering subset; this explicit
//! semantic family grants no subset receipt or producer/proof authority.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, run_rust, semr_target};
use trust_ir::inst::{BinOp, CastOp};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode,
    Module, TupleLayoutDescriptor, Ty, TyId, ValueId,
};

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn n(inst: Inst, id: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(id))
}
fn item(id: u32) -> Ty {
    Ty::FnItem(FuncId::new(id))
}
fn literal(id: u32, result: u32) -> InstrNode {
    n(
        Inst::Const {
            ty: item(id),
            value: Constant::FnItem(FuncId::new(id)),
        },
        result,
    )
}
fn call(operand: u32, result: u32) -> InstrNode {
    n(
        Inst::CallIndirect {
            callee: v(operand),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        result,
    )
}
fn ret(id: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![v(id)],
    })
}
fn function(module: &mut Module, id: u32, name: &str, params: Vec<Ty>, body: Vec<InstrNode>) {
    let wanted = FuncTy::unrecorded(params.clone(), vec![Ty::U32], false);
    let signature = module
        .func_types
        .iter()
        .position(|signature| signature == &wanted)
        .map(|position| FuncTyId::new(u32::try_from(position).unwrap()))
        .unwrap_or_else(|| module.add_func_type(wanted).unwrap());
    let mut function = Function::new(FuncId::new(id), name, signature, BlockId::new(0));
    function.blocks.push(Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(i, ty)| (v(i as u32), ty))
            .collect(),
        body,
    });
    module.try_add_function(function).unwrap();
}

fn base(bits: u32) -> Module {
    let mut module = Module::new(format!("nominal_items_{bits}"));
    module.target_info = Some(semr_target(bits));
    for (id, answer) in [(11, 1), (53, 2)] {
        function(
            &mut module,
            id,
            &format!("target_{id}"),
            vec![],
            vec![
                n(
                    Inst::Const {
                        ty: Ty::U32,
                        value: Constant::Int(answer),
                    },
                    0,
                ),
                ret(0),
            ],
        );
    }
    assert_eq!(module.functions[0].ty, module.functions[1].ty);
    assert_eq!(module.functions[0].ty, FuncTyId::new(0));
    for (wrapper, target) in [(101, 11), (103, 53)] {
        function(
            &mut module,
            wrapper,
            &format!("apply_{target}"),
            vec![item(target)],
            vec![call(0, 1), ret(1)],
        );
    }
    module
}

#[derive(Clone)]
struct Run {
    id: FuncId,
    expected: Verdict,
}

fn positives(bits: u32) -> (Module, Vec<Run>) {
    let mut module = base(bits);
    let tuple = Ty::Tuple(vec![item(11), item(53)]);
    module.types.push(tuple.clone());
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(0),
        size: 0,
        align: 1,
        field_offsets: vec![0, 0],
    });
    function(
        &mut module,
        201,
        "tuple_two_wrappers_compute_twelve",
        vec![],
        vec![
            n(
                Inst::Const {
                    ty: tuple,
                    value: Constant::Aggregate(vec![
                        Constant::FnItem(FuncId::new(11)),
                        Constant::FnItem(FuncId::new(53)),
                    ]),
                },
                0,
            ),
            n(
                Inst::ExtractField {
                    ty: item(11),
                    aggregate: v(0),
                    field: 0,
                },
                1,
            ),
            n(
                Inst::ExtractField {
                    ty: item(53),
                    aggregate: v(0),
                    field: 1,
                },
                2,
            ),
            n(
                Inst::Call {
                    callee: FuncId::new(101),
                    args: vec![v(1)],
                },
                3,
            ),
            n(
                Inst::Call {
                    callee: FuncId::new(103),
                    args: vec![v(2)],
                },
                4,
            ),
            n(
                Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(10),
                },
                5,
            ),
            n(
                Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::U32,
                    lhs: v(3),
                    rhs: v(5),
                },
                6,
            ),
            n(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U32,
                    lhs: v(6),
                    rhs: v(4),
                },
                7,
            ),
            ret(7),
        ],
    );
    function(
        &mut module,
        202,
        "zero_byte_cast_selects_destination",
        vec![],
        vec![
            literal(11, 0),
            n(
                Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: item(11),
                    dst_ty: item(53),
                    operand: v(0),
                },
                1,
            ),
            call(1, 2),
            ret(2),
        ],
    );
    function(
        &mut module,
        203,
        "same_item_reifies_to_pointer",
        vec![],
        vec![
            literal(11, 0),
            n(
                Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: item(11),
                    dst_ty: Ty::Func(FuncTyId::new(0)),
                    operand: v(0),
                },
                1,
            ),
            call(1, 2),
            ret(2),
        ],
    );
    function(
        &mut module,
        204,
        "zero_byte_load_reconstructs_item",
        vec![],
        vec![
            n(
                Inst::Alloca {
                    ty: item(53),
                    count: None,
                    align: None,
                },
                0,
            ),
            n(
                Inst::Load {
                    ty: item(53),
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
                1,
            ),
            call(1, 2),
            ret(2),
        ],
    );
    function(
        &mut module,
        205,
        "unused_undef_item_is_ub",
        vec![],
        vec![
            n(Inst::Undef { ty: item(11) }, 0),
            n(
                Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(1),
                },
                1,
            ),
            ret(1),
        ],
    );
    function(
        &mut module,
        206,
        "inspected_undef_item_is_ub",
        vec![],
        vec![n(Inst::Undef { ty: item(11) }, 0), call(0, 1), ret(1)],
    );
    module.types.push(item(53));
    let array = Ty::Array(TyId::new(1), u64::MAX);
    function(
        &mut module,
        207,
        "huge_zero_byte_array_load_keeps_singleton",
        vec![],
        vec![
            n(
                Inst::Alloca {
                    ty: array.clone(),
                    count: None,
                    align: None,
                },
                0,
            ),
            n(
                Inst::Load {
                    ty: array,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
                1,
            ),
            n(
                Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(i128::from(u64::MAX - 1)),
                },
                2,
            ),
            n(
                Inst::ExtractElement {
                    ty: item(53),
                    array: v(1),
                    index: v(2),
                },
                3,
            ),
            call(3, 4),
            ret(4),
        ],
    );
    let runs = [(201, 12), (202, 2), (203, 1), (204, 2), (207, 2)]
        .into_iter()
        .map(|(id, answer)| Run {
            id: FuncId::new(id),
            expected: Verdict::Ok(vec![Val::Int {
                width: 32,
                raw: answer,
            }]),
        })
        .chain([205, 206].map(|id| Run {
            id: FuncId::new(id),
            expected: Verdict::Ub(String::new()),
        }))
        .collect();
    (module, runs)
}

fn negatives(bits: u32) -> Vec<Module> {
    let mut module = base(bits);
    function(
        &mut module,
        201,
        "invalid_item_use",
        vec![],
        vec![literal(11, 0), call(0, 1), ret(1)],
    );
    let mut signature = module.clone();
    signature.name.push_str("_signature_id");
    let alias = FuncTyId::new(signature.func_types.len() as u32);
    signature.func_types.push(signature.func_types[0].clone());
    let root = signature
        .functions
        .iter_mut()
        .find(|f| f.id == FuncId::new(201))
        .unwrap();
    if let Inst::CallIndirect { sig, .. } = &mut root.blocks[0].body[1].inst {
        *sig = alias;
    } else {
        unreachable!();
    }
    let mut convention = module.clone();
    convention.name.push_str("_calling_convention");
    let root = convention
        .functions
        .iter_mut()
        .find(|f| f.id == FuncId::new(201))
        .unwrap();
    if let Inst::CallIndirect { calling_conv, .. } = &mut root.blocks[0].body[1].inst {
        *calling_conv = CallingConv::Rust;
    } else {
        unreachable!();
    }
    let mut forged = module.clone();
    forged.name.push_str("_wrong_constant_identity");
    let root = forged
        .functions
        .iter_mut()
        .find(|f| f.id == FuncId::new(201))
        .unwrap();
    if let Inst::Const { value, .. } = &mut root.blocks[0].body[0].inst {
        *value = Constant::FnItem(FuncId::new(53));
    } else {
        unreachable!();
    }
    let mut missing = module.clone();
    missing.name.push_str("_missing_header");
    missing.functions.retain(|f| f.id != FuncId::new(11));
    let mut duplicate = module;
    duplicate.name.push_str("_duplicate_header");
    duplicate.functions.push(duplicate.functions[0].clone());
    vec![signature, convention, forged, missing, duplicate]
}

fn codec_attempts(module: Module) -> [(&'static str, Result<Module, String>); 5] {
    let binary = trust_ir::binary::serialize_module(&module)
        .map_err(|error| error.to_string())
        .and_then(|bytes| {
            trust_ir::binary::deserialize_module(&bytes).map_err(|error| error.to_string())
        });
    let text = trust_ir::format::text_checked(&module)
        .map_err(|error| error.to_string())
        .and_then(|text| trust_ir::parser::parse_module(&text).map_err(|error| error.to_string()));
    let json = serde_json::to_vec(&module)
        .map_err(|error| error.to_string())
        .and_then(|bytes| serde_json::from_slice(&bytes).map_err(|error| error.to_string()));
    let message_pack = rmp_serde::to_vec_named(&module)
        .map_err(|error| error.to_string())
        .and_then(|bytes| rmp_serde::from_slice(&bytes).map_err(|error| error.to_string()));
    [
        ("original", Ok(module)),
        ("binary", binary),
        ("text", text),
        ("JSON", json),
        ("MessagePack", message_pack),
    ]
}

fn codeced(module: Module) -> [(&'static str, Module); 5] {
    codec_attempts(module).map(|(codec, result)| {
        (
            codec,
            result.unwrap_or_else(|error| panic!("{codec}: {error}")),
        )
    })
}

struct NegativeCell {
    label: String,
    codec: &'static str,
    duplicate: bool,
    decoded: Result<Module, String>,
}

fn negative_cells() -> Vec<NegativeCell> {
    let cells: Vec<_> = [32, 64]
        .into_iter()
        .flat_map(negatives)
        .flat_map(|module| {
            let label = module.name.clone();
            let duplicate = label.ends_with("_duplicate_header");
            codec_attempts(module).map(move |(codec, decoded)| NegativeCell {
                label: format!("{label}/{codec}"),
                codec,
                duplicate,
                decoded,
            })
        })
        .collect();
    assert_eq!(cells.len(), 50);
    cells
}

fn assert_text_duplicate_refusal(cell: &NegativeCell, error: &str) {
    assert!(
        cell.duplicate && cell.codec == "text",
        "{}: {error}",
        cell.label
    );
    assert!(
        error.contains("duplicate-function-id"),
        "{}: {error}",
        cell.label
    );
}

fn expected(actual: &Verdict, expected: &Verdict) {
    match expected {
        Verdict::Ub(_) => assert!(matches!(actual, Verdict::Ub(_)), "{actual:?}"),
        _ => assert_eq!(actual, expected),
    }
}

#[test]
fn nominal_function_item_fixtures_have_exact_rust_verdicts() {
    let mut counts = [0, 0, 0];
    for bits in [32, 64] {
        let (module, runs) = positives(bits);
        for (_, module) in codeced(module) {
            assert!(trust_ir_build::validate_module(&module).is_empty());
            for run in &runs {
                expected(&run_rust(&module, run.id, &[]), &run.expected);
                counts[0] += 1;
            }
        }
    }
    for cell in negative_cells() {
        match &cell.decoded {
            Ok(module) => {
                assert!(!trust_ir_build::validate_module(module).is_empty());
                assert!(
                    matches!(
                        run_rust(module, FuncId::new(201), &[]),
                        Verdict::TypeError(_)
                    ),
                    "{}",
                    cell.label
                );
                counts[1] += 1;
            }
            Err(error) => {
                assert_text_duplicate_refusal(&cell, error);
                counts[2] += 1;
            }
        }
    }
    assert_eq!(counts, [70, 48, 2]);
}

#[test]
fn nominal_function_items_execute_from_decoded_modules_across_codecs() {
    let modules: Vec<_> = [32, 64]
        .into_iter()
        .flat_map(|bits| {
            let (module, runs) = positives(bits);
            codeced(module)
                .into_iter()
                .map(move |(codec, module)| (format!("{bits}/{codec}"), module, runs.clone()))
        })
        .collect();
    for (_, module, _) in &modules {
        assert!(trust_ir_build::validate_module(module).is_empty());
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.iter().map(|run| (run.id, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 70);
    for (report, run) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        expected(&report.rust, &run.expected);
        expected(&report.lean, &run.expected);
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[test]
fn nominal_function_item_header_refusals_are_paired_runtime_errors() {
    let cells = negative_cells();
    let mut parsed = Vec::new();
    let mut transport_refusals = 0;
    for cell in &cells {
        match &cell.decoded {
            Ok(module) => {
                assert!(!trust_ir_build::validate_module(module).is_empty());
                parsed.push((cell.label.as_str(), module));
            }
            Err(error) => {
                assert_text_duplicate_refusal(cell, error);
                transport_refusals += 1;
            }
        }
    }
    assert_eq!((parsed.len(), transport_refusals), (48, 2));
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = parsed
        .iter()
        .map(|(label, module)| Batch {
            label: (*label).into(),
            module,
            runs: vec![(FuncId::new(201), vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 48);
    for report in reports {
        assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
        assert!(matches!(report.lean, Verdict::TypeError(_)), "{report:?}");
        // The maintained comparator does not call malformed-input TypeErrors
        // agreement. Two text cells are transport refusals before execution.
        assert!(
            matches!(report.comparison, Comparison::Mismatch(_)),
            "{report:?}"
        );
    }
}
