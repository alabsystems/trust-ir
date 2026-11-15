// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Transport, ordinary call typing, and fail-closed model controls. These are
//! TEST-rung checks, not proof of source FnAbi or native unwinding behavior.

use trust_ir::interpret::{InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{
    CallTarget, CallUnwindDisposition, CallingConv, FuncId, FuncTyId, Inst, Module, Ty, ValueId,
};
use trust_ir_build::{ValidationError, validate_module};
use trust_ir_conformance::fixtures::build_call_unwind_boundary;

fn fixture() -> Module {
    let m = build_call_unwind_boundary().expect("typed call fixture");
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    m
}

fn ordinary(mut m: Module) -> Module {
    for node in &mut m.functions[1].blocks[0].body {
        node.inst = match &node.inst {
            Inst::CallCannotUnwind { callee, args } => Inst::Call {
                callee: *callee,
                args: args.clone(),
            },
            Inst::CallIndirectCannotUnwind {
                callee, sig, args, ..
            } => Inst::CallIndirect {
                callee: *callee,
                sig: *sig,
                args: args.clone(),
                calling_conv: CallingConv::C,
            },
            other => other.clone(),
        };
    }
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    m
}

#[test]
fn call_unwind_boundary_borrowed_shapes_operands_effects_and_result_types() {
    let m = fixture();
    for (index, node) in m.functions[1].blocks[0].body[..4].iter().enumerate() {
        let shape = node.inst.call_shape().expect("four actual call variants");
        assert_eq!(shape.args, &[ValueId(21 + index as u32)]);
        assert_eq!(
            shape.unwind,
            if index % 2 == 0 {
                CallUnwindDisposition::Propagate
            } else {
                CallUnwindDisposition::CannotUnwind
            }
        );
        let mut operands = Vec::new();
        node.inst.visit_value_operands(|value| operands.push(value));
        if index < 2 {
            assert_eq!(shape.target, CallTarget::Direct(FuncId(0)));
            assert_eq!(operands, shape.args);
        } else {
            assert_eq!(
                shape.target,
                CallTarget::Indirect {
                    callee: ValueId(20),
                    sig: FuncTyId(0),
                    calling_conv: if index == 2 {
                        CallingConv::C
                    } else {
                        CallingConv::Fast
                    },
                }
            );
            assert_eq!(operands, [ValueId(20), ValueId(21 + index as u32)]);
        }
        assert!(node.inst.has_observable_effects());
        assert!(!node.inst.is_terminator());
        assert_eq!(node.results, [ValueId(22 + index as u32)]);
    }
    assert!(m.functions[1].blocks[0].body[4].inst.call_shape().is_none());
}

#[test]
fn call_unwind_boundary_all_four_codecs_preserve_distinct_semantics() {
    let m = fixture();
    let bin = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    assert_eq!(trust_ir::binary::deserialize_module(&bin).unwrap(), m);
    let json = serde_json::to_vec(&m).unwrap();
    assert_eq!(serde_json::from_slice::<Module>(&json).unwrap(), m);
    let msgpack = rmp_serde::to_vec(&m).unwrap();
    assert_eq!(rmp_serde::from_slice::<Module>(&msgpack).unwrap(), m);
    let text = trust_ir::format::canonical(&m);
    assert!(text.contains("call_cannot_unwind"));
    assert!(text.contains("call_indirect_cannot_unwind"));
    assert_eq!(
        trust_ir::parser::parse_module(&text).unwrap(),
        trust_ir::format::canonicalize(&m)
    );
}

#[test]
fn call_unwind_boundary_same_payload_is_not_a_proof_insensitive_diff_or_identity() {
    let m = fixture();
    let mut old = m.clone();
    // Preserve every operand, signature and convention; vary only the opcode.
    for node in &mut old.functions[1].blocks[0].body {
        node.inst = match &node.inst {
            Inst::CallCannotUnwind { callee, args } => Inst::Call {
                callee: *callee,
                args: args.clone(),
            },
            Inst::CallIndirectCannotUnwind {
                callee,
                sig,
                args,
                calling_conv,
            } => Inst::CallIndirect {
                callee: *callee,
                sig: *sig,
                args: args.clone(),
                calling_conv: *calling_conv,
            },
            other => other.clone(),
        };
    }
    assert!(validate_module(&old).is_empty());
    assert!(
        !trust_ir::diff::diff_with(
            &m,
            &old,
            trust_ir::diff::DiffOptions {
                ignore_proofs: true,
                include_debug: false,
            }
        )
        .is_empty()
    );
    assert_ne!(m.stable_digest(), old.stable_digest());
    assert_ne!(
        m.executable_content_digest_v1(),
        old.executable_content_digest_v1()
    );
    assert_ne!(
        m.source_provenance_semantic_digest(FuncId(1)),
        old.source_provenance_semantic_digest(FuncId(1))
    );
    let canonical = trust_ir::format::canonicalize(&m);
    // Stable wire identity retains actual stored SSA; semantic diff and the
    // executable canonical identity, not that raw identity, ignore renumbering.
    assert!(trust_ir::diff::diff(&m, &canonical).is_empty());
    assert_eq!(
        m.executable_content_digest_v1(),
        canonical.executable_content_digest_v1()
    );
}

#[test]
fn call_unwind_boundary_structural_typing_still_refuses_wrong_actual_inputs() {
    let m = fixture();
    let mut wrong = m.clone();
    let Inst::CallCannotUnwind { callee, .. } = &mut wrong.functions[1].blocks[0].body[1].inst
    else {
        panic!("direct boundary")
    };
    *callee = FuncId(999);
    assert!(
        validate_module(&wrong)
            .iter()
            .any(|e| matches!(e, ValidationError::CalleeNotFound { callee_id: 999, .. }))
    );
    let mut wrong = m.clone();
    let Inst::CallCannotUnwind { args, .. } = &mut wrong.functions[1].blocks[0].body[1].inst else {
        panic!("direct boundary")
    };
    args.clear();
    assert!(
        validate_module(&wrong)
            .iter()
            .any(|e| matches!(e, ValidationError::CallArgCountMismatch { .. }))
    );
    let mut wrong = m.clone();
    let Inst::CallCannotUnwind { args, .. } = &mut wrong.functions[1].blocks[0].body[1].inst else {
        panic!("direct boundary")
    };
    args[0] = ValueId(20);
    assert!(
        validate_module(&wrong)
            .iter()
            .any(|e| matches!(e, ValidationError::CallArgTypeMismatch { .. }))
    );
    let mut wrong = m.clone();
    let Inst::CallIndirectCannotUnwind { sig, .. } = &mut wrong.functions[1].blocks[0].body[3].inst
    else {
        panic!("indirect boundary")
    };
    *sig = FuncTyId(999);
    assert!(validate_module(&wrong).iter().any(|e| matches!(
        e,
        ValidationError::CallIndirectSigNotFound { sig_id: 999, .. }
    )));
    let mut wrong = m.clone();
    let Inst::CallIndirectCannotUnwind { args, .. } =
        &mut wrong.functions[1].blocks[0].body[3].inst
    else {
        panic!("indirect boundary")
    };
    args[0] = ValueId(20);
    assert!(
        validate_module(&wrong)
            .iter()
            .any(|e| matches!(e, ValidationError::CallIndirectArgTypeMismatch { .. }))
    );
}

#[test]
fn call_unwind_boundary_no_eh_reference_model_refuses_even_a_returning_callee() {
    let m = fixture();
    let old = ordinary(m.clone());
    let args = || {
        [
            InterpretValue {
                ty: Ty::Func(FuncTyId(0)),
                kind: InterpretValueKind::FnDef(FuncId(0)),
            },
            InterpretValue::int(Ty::U64, 37).unwrap(),
        ]
    };
    let outcome = Interpreter::with_module(&old)
        .execute_func(FuncId(1), args())
        .unwrap();
    assert_eq!(outcome.returns, [InterpretValue::int(Ty::U64, 37).unwrap()]);
    let error = Interpreter::with_module(&m)
        .execute_func(FuncId(1), args())
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedInstruction);
    assert!(error.message.contains("no host-unwind boundary model"));
    assert_eq!(error.block, Some(trust_ir::BlockId(11)));
    let mut indirect_only = m.clone();
    let Inst::CallCannotUnwind {
        callee,
        args: call_args,
    } = &indirect_only.functions[1].blocks[0].body[1].inst
    else {
        panic!("boundary")
    };
    indirect_only.functions[1].blocks[0].body[1].inst = Inst::Call {
        callee: *callee,
        args: call_args.clone(),
    };
    assert!(validate_module(&indirect_only).is_empty());
    let error = Interpreter::with_module(&indirect_only)
        .execute_func(FuncId(1), args())
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedInstruction);
    assert!(error.message.contains("no host-unwind boundary model"));
}

#[test]
fn call_unwind_boundary_no_eh_core_and_proven_subset_refuse_without_new_authority() {
    let mut m = fixture();
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let addresses = [(FuncId(0), 4096), (FuncId(1), 8192)];
    let old = ordinary(m.clone());
    assert!(trust_ir_build::core_reflection::reflect_core_module_v1(&old, &addresses).is_ok());
    let error = trust_ir_build::core_reflection::reflect_core_module_v1(&m, &addresses)
        .expect_err("host unwind is not modeled");
    assert!(
        error
            .to_string()
            .contains("call unwind boundary requires a host-unwind semantic rule"),
        "{error}"
    );
    let errors = trust_ir_conformance::subset::module_subset_violations(&m);
    assert!(errors.iter().any(|e| e.contains("CallCannotUnwind")));
    assert!(
        errors
            .iter()
            .any(|e| e.contains("CallIndirectCannotUnwind"))
    );
    let report = trust_ir_build::validate::validate_module_report(&m);
    assert_eq!(report.unwind_surface(), [FuncId(1)]);
    assert!(m.proof_obligations.is_empty());
    assert!(m.proof_certificates.is_empty());
}

#[test]
fn call_unwind_boundary_exact_callee_convention_and_weak_origin_still_bind() {
    let mut m = fixture();
    let caller_sig = m.functions[1].ty;
    m.func_types[caller_sig.as_usize()].params.remove(0);
    let block = &mut m.functions[1].blocks[0];
    block.params.remove(0);
    let mut address = trust_ir::InstrNode::new(Inst::Const {
        ty: Ty::Func(FuncTyId(0)),
        value: trust_ir::Constant::FnDef(FuncId(0)),
    });
    address.results.push(ValueId(20));
    block.body.insert(0, address);
    let Inst::CallIndirectCannotUnwind { calling_conv, .. } = &mut block.body[4].inst else {
        panic!("boundary")
    };
    *calling_conv = CallingConv::C;
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let mut wrong = m.clone();
    let Inst::CallIndirectCannotUnwind { calling_conv, .. } =
        &mut wrong.functions[1].blocks[0].body[4].inst
    else {
        panic!("boundary")
    };
    *calling_conv = CallingConv::Fast;
    assert!(
        validate_module(&wrong)
            .iter()
            .any(|e| matches!(e, ValidationError::CallEdgeConvMismatch { .. }))
    );
    let mut weak = fixture();
    weak.functions[0].blocks.clear();
    weak.functions[0].linkage = trust_ir::Linkage::ExternalWeak;
    assert!(
        validate_module(&weak)
            .iter()
            .any(|e| matches!(e, ValidationError::DirectCallToWeakDeclaration { .. }))
    );
}

#[test]
fn call_unwind_boundary_source_custody_and_dependency_coordinates_remain_exact() {
    use trust_ir::function_dependencies::{
        DependencyNode, DependencySite, inspect_function_dependencies,
    };
    let mut m = fixture();
    let graph = inspect_function_dependencies(&m, FuncId(1));
    assert_eq!(graph.root(), FuncId(1));
    for index in [0, 1] {
        assert!(graph.edges().iter().any(|edge| edge.target
            == DependencyNode::Function(FuncId(0))
            && edge.site
                == DependencySite::Instruction {
                    function: FuncId(1),
                    block: trust_ir::BlockId(11),
                    index,
                }));
    }
    for index in [2, 3] {
        assert!(graph.edges().iter().any(|edge| edge.target
            == DependencyNode::FunctionType(FuncTyId(0))
            && edge.site
                == DependencySite::Instruction {
                    function: FuncId(1),
                    block: trust_ir::BlockId(11),
                    index,
                }));
    }
    let source = trust_ir::proof::ProofDigest::sha256_domain(
        "trust_ir.test.call_boundary",
        b"compiler source fixture",
    );
    // A source-loop carrier is legal only for a real reachable natural loop.
    // Preserve the call sites and add a finite zero-iteration loop route.
    let header_id = trust_ir::BlockId(12);
    let exit_id = trust_ir::BlockId(13);
    m.functions[1].blocks[0].body[4].inst = Inst::Br {
        target: header_id,
        args: vec![],
    };
    let mut header = trust_ir::Block::new(header_id);
    let mut condition = trust_ir::InstrNode::new(Inst::Const {
        ty: Ty::Bool,
        value: trust_ir::Constant::Bool(false),
    });
    condition.results.push(ValueId(26));
    header.body.push(condition);
    header.body.push(trust_ir::InstrNode::new(Inst::CondBr {
        cond: ValueId(26),
        then_target: header_id,
        then_args: vec![],
        else_target: exit_id,
        else_args: vec![],
    }));
    let mut exit = trust_ir::Block::new(exit_id);
    exit.body.push(trust_ir::InstrNode::new(Inst::Return {
        values: vec![ValueId(25)],
    }));
    m.functions[1].blocks.extend([header, exit]);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let body = m.source_provenance_semantic_digest(FuncId(1)).unwrap();
    m.functions[1].source_provenance = Some(trust_ir::SourceProvenance::new(
        source,
        body,
        vec![trust_ir::SourceLoopProvenance {
            source_loop_id: 0,
            hir_local_id: 1,
            header: header_id,
            bindings: vec![],
        }],
    ));
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let Inst::CallCannotUnwind { callee, args } = &m.functions[1].blocks[0].body[1].inst else {
        panic!("boundary")
    };
    m.functions[1].blocks[0].body[1].inst = Inst::Call {
        callee: *callee,
        args: args.clone(),
    };
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidSourceProvenance { .. }))
    );
}
