// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment D, Part 1 (wire v55, `docs/SPEC_RATIFICATIONS.md` §20): what the
// validator does with the module drop-glue table, with drop sites and with
// `Inst::DropInvoke`.
//
//   * T1-T7 (`InvalidDropGlue`): the glue names one function whose signature
//     is exactly `(ptr) -> ()` non-variadic; it is not weak and not a pinned
//     runtime entry; rows strictly ascend by glue; one row per type; the key
//     is neither a refinement nor trivially droppable;
//   * S1-S3 (`NonCanonicalDrop`): no drop of a refined or trivially droppable
//     type; a registered glue is never called directly (call, invoke,
//     call_cannot_unwind, seq_map, panic-site entry) — its address is fine;
//   * the drop operand is exactly `Ptr` (`OperandTypeMismatch`);
//   * an unresolved drop is well-formed, reported, and refused by the codegen
//     gate (`UnlowerableForCodegen`); a resolved one is admitted;
//   * `DropInvoke` has `Invoke`'s unwind and edge discipline and joins the
//     unwind surface;
//   * a resolved drop is a call node (proof contexts, memory claims) whose
//     callee is its glue.

use trust_ir::proof::{ObligationKind, ProofContext, ProofObligation, ProofStatus};
use trust_ir::ty::{FieldDef, FuncTy, StructDef, StructRepr};
use trust_ir::value::{GlobalId, ProofId, StructId};
use trust_ir::{
    AssertKind, Block, BlockId, CallingConv, Constant, Endianness, FuncId, Function, Inst,
    InstrNode, Linkage, Module, PanicLocation, PanicSite, TargetInfo, Ty, ValueId,
};
use trust_ir_build::validate::{
    ValidationError, codegen_lowerability_errors, validate_module_report,
};
use trust_ir_build::validate_module;

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}
fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

/// The canonical 64-bit target: a bodyless declaration is admitted only on a
/// known target.
fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn ret() -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![] })
}

/// A module with two owning structs `S0`, `S1` (`{ data: ptr }`), the
/// signature table `functy.0 = (ptr) -> ()`, and a defined glue for each
/// (`drop_s0` @func.0, `drop_s1` @func.1) whose body returns. The table is
/// EMPTY: tests state the rows they need.
fn base() -> Module {
    let mut m = Module::new("drop_glue");
    m.target_info = Some(target());
    for id in 0..2 {
        m.add_struct(StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: vec![FieldDef {
                name: "data".into(),
                ty: Ty::Ptr,
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::default(),
            origin: None,
        });
    }
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (id, name) in [(0, "drop_s0"), (1, "drop_s1")] {
        let mut glue = Function::new(FuncId::new(id), name, sig, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(ret());
        glue.blocks.push(block);
        m.try_add_function(glue)
            .expect("Module::try_add_function: test fixture");
    }
    m
}

/// `base()` with both rows stated.
fn with_table() -> Module {
    let mut m = base();
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    m.set_drop_glue(s(1), FuncId::new(1)).unwrap();
    m
}

/// Append `f(%0: param) { body..; ret }` as @func.<next>, returning its id.
fn add_caller(m: &mut Module, param: Ty, body: Vec<InstrNode>) -> FuncId {
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![param.clone()],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(m.functions.len() as u32);
    let mut f = Function::new(id, format!("caller{}", id.index()), sig, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), param));
    block.body.extend(body);
    block.body.push(ret());
    f.blocks.push(block);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    id
}

/// Append a caller whose body is `drop_invoke ty, %0 to bb1(normal_args)
/// unwind bb2`, with `bb1(%1: ptr)` returning and `bb2` a cleanup pad that
/// resumes (or, when `pad` is false, an ordinary `unreachable` block).
fn add_drop_invoke_caller(m: &mut Module, ty: Ty, pad: bool, unwind: BlockId) -> FuncId {
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(m.functions.len() as u32);
    let mut f = Function::new(id, format!("cleanup{}", id.index()), sig, b(0));
    let mut entry = Block::new(b(0));
    entry.params.push((v(0), Ty::Ptr));
    entry.body.push(InstrNode::new(Inst::DropInvoke {
        ty,
        ptr: v(0),
        normal_dest: b(1),
        normal_args: vec![v(0)],
        unwind_dest: unwind,
    }));
    f.blocks.push(entry);
    let mut normal = Block::new(b(1));
    normal.params.push((v(1), Ty::Ptr));
    normal.body.push(ret());
    f.blocks.push(normal);
    let mut cleanup = Block::new(b(2));
    if pad {
        cleanup.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .with_results(vec![v(2), v(3)]),
        );
        cleanup
            .body
            .push(InstrNode::new(Inst::Resume { exn: v(2) }));
    } else {
        cleanup.body.push(InstrNode::new(Inst::Unreachable));
    }
    f.blocks.push(cleanup);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    id
}

fn drop_node(ty: Ty) -> InstrNode {
    InstrNode::new(Inst::Drop { ty, ptr: v(0) })
}

fn invalid_glue(errors: &[ValidationError]) -> Vec<(usize, String)> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::InvalidDropGlue { entry, reason, .. } => {
                Some((*entry, reason.clone()))
            }
            _ => None,
        })
        .collect()
}

fn non_canonical(errors: &[ValidationError]) -> Vec<String> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::NonCanonicalDrop { reason, .. } => Some(reason.clone()),
            _ => None,
        })
        .collect()
}

#[test]
fn a_well_formed_drop_glue_table_validates() {
    let mut m = with_table();
    add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0)), drop_node(s(1))]);
    add_drop_invoke_caller(&mut m, s(1), true, b(2));
    // A drop of an array of droppable structs is not trivially droppable,
    // and is unresolved without its own row (keys are compared by derived
    // equality): still well-formed.
    let elem = m.add_type(s(0)).expect("Module::add_type: test fixture");
    add_caller(&mut m, Ty::Ptr, vec![drop_node(Ty::Array(elem, 2))]);
    assert_eq!(validate_module(&m), vec![], "the control must validate");
    // A bodyless, non-weak glue declaration is admitted too.
    let mut m = base();
    m.functions[1].blocks.clear();
    m.set_drop_glue(s(1), FuncId::new(1)).unwrap();
    assert_eq!(validate_module(&m), vec![]);
}

#[test]
fn a_glue_with_the_wrong_signature_is_invalid_drop_glue() {
    for (params, returns, vararg) in [
        (vec![Ty::I64], vec![], false),
        (vec![Ty::Ptr], vec![Ty::I32], false),
        (vec![Ty::Ptr, Ty::Ptr], vec![], false),
        (vec![], vec![], false),
        (vec![Ty::Ptr], vec![], true),
    ] {
        let mut m = base();
        let sig = m
            .add_func_type(FuncTy {
                abi: None,
                params: params.clone(),
                returns: returns.clone(),
                is_vararg: vararg,
            })
            .expect("Module::add_func_type: test fixture");
        // Re-sign glue @func.0 as a bodyless declaration (its body would
        // otherwise disagree with the new signature).
        m.functions[0].ty = sig;
        m.functions[0].blocks.clear();
        m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
        let refused = invalid_glue(&validate_module(&m));
        assert!(
            refused
                .iter()
                .any(|(entry, reason)| *entry == 0 && reason.contains("exactly (ptr) -> ()")),
            "{params:?} -> {returns:?} (vararg {vararg}) must be InvalidDropGlue, got {refused:?}"
        );
    }
}

#[test]
fn a_glue_naming_no_function_is_invalid_drop_glue() {
    let mut m = base();
    m.set_drop_glue(s(0), FuncId::new(99)).unwrap();
    let refused = invalid_glue(&validate_module(&m));
    assert_eq!(refused.len(), 1, "{refused:?}");
    assert!(refused[0].1.contains("names no function"), "{refused:?}");
}

#[test]
fn a_weak_or_pinned_runtime_glue_is_invalid_drop_glue() {
    // A weak declaration: its address may be null.
    let mut m = base();
    m.functions[0].blocks.clear();
    m.functions[0].linkage = Linkage::ExternalWeak;
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    let refused = invalid_glue(&validate_module(&m));
    assert!(
        refused
            .iter()
            .any(|(_, reason)| reason.contains("weak declaration")),
        "{refused:?}"
    );
    // A pinned runtime entry: `clean_dec` is `(ptr) -> ()`, but it takes a
    // reference-counted cell, not a place.
    let mut m = base();
    m.functions[0].blocks.clear();
    m.functions[0].name = "clean_dec".into();
    m.functions[0].calling_conv = CallingConv::C;
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    let refused = invalid_glue(&validate_module(&m));
    assert!(
        refused
            .iter()
            .any(|(_, reason)| reason.contains("pinned runtime entry")),
        "{refused:?}"
    );
}

#[test]
fn drop_glue_rows_are_canonically_ordered_injective_and_unique_by_type() {
    let canonical = with_table();
    let rows = canonical.drop_glue.clone();
    assert!(invalid_glue(&validate_module(&canonical)).is_empty());

    let mut descending = canonical.clone();
    descending.drop_glue = vec![rows[1].clone(), rows[0].clone()];
    let refused = invalid_glue(&validate_module(&descending));
    assert!(
        refused
            .iter()
            .any(|(entry, reason)| *entry == 1 && reason.contains("strictly ascending")),
        "{refused:?}"
    );

    let mut one_glue_two_types = canonical.clone();
    one_glue_two_types.drop_glue[1].glue = rows[0].glue;
    let refused = invalid_glue(&validate_module(&one_glue_two_types));
    assert!(
        refused
            .iter()
            .any(|(entry, reason)| *entry == 1 && reason.contains("strictly ascending")),
        "{refused:?}"
    );

    let mut one_type_two_glues = canonical;
    one_type_two_glues.drop_glue[1].ty = rows[0].ty.clone();
    let refused = invalid_glue(&validate_module(&one_type_two_glues));
    assert!(
        refused
            .iter()
            .any(|(entry, reason)| *entry == 1 && reason.contains("one row per type")),
        "{refused:?}"
    );

    // The sanctioned constructor refuses both conflicts up front.
    let mut m = base();
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    assert!(m.set_drop_glue(s(0), FuncId::new(1)).is_err());
    assert!(m.set_drop_glue(s(1), FuncId::new(0)).is_err());
    assert!(
        m.set_drop_glue(s(0), FuncId::new(0)).is_ok(),
        "re-stating is a no-op"
    );
}

#[test]
fn a_refinement_or_trivially_droppable_key_is_invalid_drop_glue() {
    let mut keys = vec![
        Ty::I32,
        Ty::Ptr,
        Ty::RefMut(Box::new(s(0))),
        Ty::Tuple(vec![Ty::U8, Ty::Ptr]),
    ];
    let mut m = base();
    let elem = m.add_type(s(0)).expect("Module::add_type: test fixture");
    keys.push(Ty::Array(elem, 0));
    let base_ty = m.add_type(s(0)).expect("Module::add_type: test fixture");
    let pred = m
        .intern_pred(trust_ir::Pred::NonNull)
        .expect("Module::intern_pred: test fixture")
        .unwrap();
    keys.push(Ty::Refine(base_ty, pred));
    for key in keys {
        let mut m = m.clone();
        m.set_drop_glue(key.clone(), FuncId::new(0)).unwrap();
        let refused = invalid_glue(&validate_module(&m));
        assert!(
            refused
                .iter()
                .any(|(_, reason)| reason.contains("trivially droppable")
                    || reason.contains("refinement")),
            "key {key} must be InvalidDropGlue, got {refused:?}"
        );
    }
}

#[test]
fn a_drop_of_a_trivially_droppable_or_refined_type_is_non_canonical() {
    let mut m = base();
    let elem = m.add_type(s(0)).expect("Module::add_type: test fixture");
    let base_ty = m.add_type(s(0)).expect("Module::add_type: test fixture");
    let pred = m
        .intern_pred(trust_ir::Pred::NonNull)
        .expect("Module::intern_pred: test fixture")
        .unwrap();
    for ty in [
        Ty::U64,
        Ty::Ptr,
        Ty::Unit,
        Ty::Tuple(vec![Ty::I32, Ty::Bool]),
        Ty::Array(elem, 0),
        Ty::Refine(base_ty, pred),
    ] {
        let mut m = m.clone();
        add_caller(&mut m, Ty::Ptr, vec![drop_node(ty.clone())]);
        let refused = non_canonical(&validate_module(&m));
        assert_eq!(refused.len(), 1, "a drop of {ty}: {refused:?}");
        let mut m2 = m.clone();
        add_drop_invoke_caller(&mut m2, ty.clone(), true, b(2));
        assert_eq!(
            non_canonical(&validate_module(&m2)).len(),
            2,
            "a drop_invoke of {ty} is refused too"
        );
    }
    // A drop of an owning struct, or a tuple holding one, is not.
    add_caller(
        &mut m,
        Ty::Ptr,
        vec![drop_node(s(0)), drop_node(Ty::Tuple(vec![Ty::I32, s(1)]))],
    );
    assert!(non_canonical(&validate_module(&m)).is_empty());
}

#[test]
fn a_direct_call_invoke_or_seq_map_of_registered_glue_is_non_canonical_and_its_address_is_not() {
    let call = |callee| {
        InstrNode::new(Inst::Call {
            callee,
            args: vec![v(0)],
        })
    };
    let cannot = |callee| {
        InstrNode::new(Inst::CallCannotUnwind {
            callee,
            args: vec![v(0)],
        })
    };
    for node in [call(FuncId::new(0)), cannot(FuncId::new(1))] {
        let mut m = with_table();
        add_caller(&mut m, Ty::Ptr, vec![node]);
        let refused = non_canonical(&validate_module(&m));
        assert_eq!(refused.len(), 1, "{refused:?}");
        assert!(refused[0].contains("registered drop glue"), "{refused:?}");
        // The same call with NO table is an ordinary call.
        let mut m = base();
        add_caller(&mut m, Ty::Ptr, vec![call(FuncId::new(0))]);
        assert!(non_canonical(&validate_module(&m)).is_empty());
    }

    // An `Invoke` of the glue.
    let mut m = with_table();
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(2), "invoker", sig, b(0));
    let mut entry = Block::new(b(0));
    entry.params.push((v(0), Ty::Ptr));
    entry.body.push(InstrNode::new(Inst::Invoke {
        callee: FuncId::new(0),
        args: vec![v(0)],
        normal_dest: b(1),
        normal_args: vec![],
        unwind_dest: b(2),
    }));
    f.blocks.push(entry);
    let mut normal = Block::new(b(1));
    normal.body.push(ret());
    f.blocks.push(normal);
    let mut pad = Block::new(b(2));
    pad.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![v(2), v(3)]),
    );
    pad.body.push(InstrNode::new(Inst::Resume { exn: v(2) }));
    f.blocks.push(pad);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    assert_eq!(
        non_canonical(&validate_module(&m)).len(),
        1,
        "invoke of glue"
    );

    // A `SeqMap` whose element function is a glue.
    let mut m = with_table();
    let elem = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    add_caller(
        &mut m,
        Ty::Sequence(elem),
        vec![
            InstrNode::new(Inst::SeqMap {
                ty: Ty::Sequence(elem),
                seq: v(0),
                fwd: FuncId::new(0),
            })
            .with_results(vec![v(1)]),
        ],
    );
    assert_eq!(
        non_canonical(&validate_module(&m)).len(),
        1,
        "seq_map of glue"
    );

    // A panic site whose entry is a glue (`(ptr) -> ()` is exactly an
    // unkinded entry's signature): its failure would call the glue directly.
    let mut m = with_table();
    m.globals.push(trust_ir::Global {
        name: "loc".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    add_caller(
        &mut m,
        Ty::Bool,
        vec![InstrNode::new(Inst::Assert {
            cond: v(0),
            kind: AssertKind::Unspecified,
            site: Some(PanicSite {
                entry: FuncId::new(0),
                location: PanicLocation::Global(GlobalId::new(0)),
            }),
        })],
    );
    assert_eq!(
        non_canonical(&validate_module(&m)).len(),
        1,
        "panic entry glue"
    );

    // Taking the glue's ADDRESS and calling it indirectly is dynamic
    // dispatch, a different construct: admitted.
    let mut m = with_table();
    let sig = FuncId::new(0);
    let glue_sig = m.functions[0].ty;
    add_caller(
        &mut m,
        Ty::Ptr,
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(glue_sig),
                value: Constant::FnDef(sig),
            })
            .with_results(vec![v(1)]),
            InstrNode::new(Inst::CallIndirect {
                callee: v(1),
                sig: glue_sig,
                args: vec![v(0)],
                calling_conv: CallingConv::default(),
            }),
        ],
    );
    let errors = validate_module(&m);
    assert!(non_canonical(&errors).is_empty(), "{errors:?}");
}

#[test]
fn the_drop_operand_must_be_exactly_ptr() {
    let mismatch = |errors: &[ValidationError], op: &str| {
        errors.iter().any(|e| {
            matches!(e, ValidationError::OperandTypeMismatch { op: o, role, .. }
                if o == op && role == "ptr")
        })
    };
    for param in [
        Ty::I64,
        Ty::RefMut(Box::new(s(0))),
        Ty::PtrMut(Box::new(s(0))),
    ] {
        let mut m = with_table();
        add_caller(&mut m, param.clone(), vec![drop_node(s(0))]);
        assert!(
            mismatch(&validate_module(&m), "drop"),
            "a drop through {param}"
        );
    }
    let mut m = with_table();
    add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0))]);
    assert!(!mismatch(&validate_module(&m), "drop"));
    // A refined pointer whose representation is `Ptr` passes, as it would
    // to a `Ptr` call parameter.
    let mut m = with_table();
    let ptr = m.add_type(Ty::Ptr).expect("Module::add_type: test fixture");
    let pred = m
        .intern_pred(trust_ir::Pred::NonNull)
        .expect("Module::intern_pred: test fixture")
        .unwrap();
    add_caller(&mut m, Ty::Refine(ptr, pred), vec![drop_node(s(0))]);
    assert!(!mismatch(&validate_module(&m), "drop"));
    // DropInvoke: same rule (its operand is %0, typed by the entry block).
    let mut m = with_table();
    let id = add_drop_invoke_caller(&mut m, s(1), true, b(2));
    let at = id.index() as usize;
    m.functions[at].blocks[0].params[0].1 = Ty::I64;
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::I64],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    m.functions[at].ty = sig;
    m.functions[at].blocks[0].body[0] = InstrNode::new(Inst::DropInvoke {
        ty: s(1),
        ptr: v(0),
        normal_dest: b(1),
        normal_args: vec![],
        unwind_dest: b(2),
    });
    m.functions[at].blocks[1].params.clear();
    assert!(mismatch(&validate_module(&m), "drop_invoke"));
}

#[test]
fn an_unresolved_drop_validates_but_is_unlowerable_for_codegen() {
    let mut m = base();
    add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0))]);
    add_drop_invoke_caller(&mut m, s(1), true, b(2));
    assert_eq!(validate_module(&m), vec![], "unresolved is well-formed");
    let refusals: Vec<_> = codegen_lowerability_errors(&m)
        .into_iter()
        .filter_map(|e| match e {
            ValidationError::UnlowerableForCodegen { inst, detail, .. } => Some((inst, detail)),
            _ => None,
        })
        .collect();
    assert_eq!(refusals.len(), 2, "{refusals:?}");
    assert_eq!(refusals[0].0, "Drop");
    assert_eq!(refusals[1].0, "DropInvoke");
    assert!(refusals[0].1.contains("no drop_glue row"), "{refusals:?}");
    assert!(refusals[0].1.contains("never lowered as nothing"));
}

#[test]
fn a_resolved_drop_is_accepted_by_the_codegen_gate() {
    let mut m = with_table();
    add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0))]);
    add_drop_invoke_caller(&mut m, s(1), true, b(2));
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(codegen_lowerability_errors(&m), vec![]);
}

#[test]
fn drop_invoke_obeys_the_invoke_unwind_structure() {
    let pad_errors = |m: &Module| -> Vec<ValidationError> {
        validate_module(m)
            .into_iter()
            .filter(|e| {
                matches!(
                    e,
                    ValidationError::UnwindDestWithoutLandingPad { .. }
                        | ValidationError::MisplacedLandingPad { .. }
                )
            })
            .collect()
    };
    let mut m = with_table();
    add_drop_invoke_caller(&mut m, s(0), true, b(2));
    assert_eq!(pad_errors(&m), vec![]);
    // (a) the unwind block has no pad.
    let mut m = with_table();
    add_drop_invoke_caller(&mut m, s(0), false, b(2));
    assert!(matches!(
        pad_errors(&m).as_slice(),
        [ValidationError::UnwindDestWithoutLandingPad { target: 2, .. }]
    ));
    // (a) the unwind block is the normal continuation.
    let mut m = with_table();
    add_drop_invoke_caller(&mut m, s(0), true, b(1));
    assert!(
        pad_errors(&m).iter().any(|e| matches!(
            e,
            ValidationError::UnwindDestWithoutLandingPad { target: 1, .. }
        )),
        "{:?}",
        pad_errors(&m)
    );
    // (b) a pad no invoke names (the DropInvoke's unwind is elsewhere) is
    // misplaced: the DropInvoke counts as an invoke, so pointing it at the
    // pad block clears the error.
    let mut m = with_table();
    let id = add_drop_invoke_caller(&mut m, s(0), true, b(2));
    let at = id.index() as usize;
    if let Inst::DropInvoke { unwind_dest, .. } = &mut m.functions[at].blocks[0].body[0].inst {
        *unwind_dest = b(3);
    }
    let mut other = Block::new(b(3));
    other.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![v(4), v(5)]),
    );
    other.body.push(InstrNode::new(Inst::Resume { exn: v(4) }));
    m.functions[at].blocks.push(other);
    let errors = pad_errors(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 2, reason }
                if reason.contains("no invoke names this block")
        )),
        "{errors:?}"
    );
}

#[test]
fn drop_invoke_edges_are_arity_checked_and_the_unwind_edge_is_parameter_free() {
    let arity = |m: &Module| {
        validate_module(m)
            .into_iter()
            .filter(|e| matches!(e, ValidationError::BranchArgCountMismatch { .. }))
            .count()
    };
    let mut m = with_table();
    let id = add_drop_invoke_caller(&mut m, s(0), true, b(2));
    assert_eq!(arity(&m), 0);
    let at = id.index() as usize;
    // The normal edge passes one argument to a block with none.
    m.functions[at].blocks[1].params.clear();
    assert_eq!(arity(&m), 1, "normal edge arity");
    // The pad block takes a parameter the unwind edge cannot bind.
    let mut m = with_table();
    let id = add_drop_invoke_caller(&mut m, s(0), true, b(2));
    let at = id.index() as usize;
    m.functions[at].blocks[2].params.push((v(9), Ty::Ptr));
    assert_eq!(arity(&m), 1, "unwind edge carries no arguments");
    // A dangling target.
    let mut m = with_table();
    let id = add_drop_invoke_caller(&mut m, s(0), true, b(2));
    let at = id.index() as usize;
    if let Inst::DropInvoke { normal_dest, .. } = &mut m.functions[at].blocks[0].body[0].inst {
        *normal_dest = b(7);
    }
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::BranchTargetNotFound { .. }))
    );
}

#[test]
fn drop_invoke_functions_are_in_the_unwind_surface() {
    let mut m = with_table();
    let plain = add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0))]);
    let cleanup = add_drop_invoke_caller(&mut m, s(0), true, b(2));
    // A function whose only unwind construct is the DropInvoke itself (its
    // "pad" is an ordinary block, so it carries no LandingPad / Resume): the
    // surface is reported regardless of the verdict, and the DropInvoke alone
    // puts the function on it.
    let bare = add_drop_invoke_caller(&mut m, s(0), false, b(2));
    let surface = validate_module_report(&m).unwind_surface();
    assert!(surface.contains(&cleanup), "{surface:?}");
    assert!(surface.contains(&bare), "the DropInvoke alone: {surface:?}");
    assert!(!surface.contains(&plain), "a plain drop is a plain call");
}

#[test]
fn unresolved_drops_are_reported() {
    let mut m = base();
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    let f = add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0)), drop_node(s(1))]);
    let g = add_drop_invoke_caller(&mut m, s(1), true, b(2));
    let report = validate_module_report(&m);
    assert_eq!(
        report.unresolved_drops(),
        vec![(f, b(0), s(1)), (g, b(0), s(1))],
        "only the drops at a type with no row"
    );
    let mut m = with_table();
    add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0))]);
    assert!(validate_module_report(&m).unresolved_drops().is_empty());
}

#[test]
fn proof_context_on_a_resolved_drop_is_scoped_to_its_glue() {
    let context_errors = |m: &Module| -> Vec<ValidationError> {
        validate_module(m)
            .into_iter()
            .filter(|e| {
                matches!(
                    e,
                    ValidationError::ProofContextOnNonCallNode { .. }
                        | ValidationError::ProofContextEstablishScopeMismatch { .. }
                )
            })
            .collect()
    };
    let module_with = |table: bool, owner: u32| {
        let mut m = if table { with_table() } else { base() };
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "the place holds an initialized S0",
            )
            .with_function(FuncId::new(owner)),
        );
        let mut node = drop_node(s(0));
        node.proof_context = Some(ProofContext {
            assumes: vec![],
            establishes: vec![ProofId::new(0)],
        });
        add_caller(&mut m, Ty::Ptr, vec![node]);
        m
    };
    // Resolved, the obligation owned by its glue: a scoped call node.
    assert_eq!(context_errors(&module_with(true, 0)), vec![]);
    // Resolved, owned by another function: a scope mismatch against the glue.
    assert!(matches!(
        context_errors(&module_with(true, 1)).as_slice(),
        [ValidationError::ProofContextEstablishScopeMismatch {
            callee: 0,
            actual_owner: 1,
            ..
        }]
    ));
    // Unresolved: no callee, so not a call node.
    assert!(matches!(
        context_errors(&module_with(false, 0)).as_slice(),
        [ValidationError::ProofContextOnNonCallNode { .. }]
    ));
}

#[test]
fn a_memory_claim_sees_a_resolved_drop_as_a_call_of_its_glue() {
    let claim_errors = |m: &Module| {
        validate_module(m)
            .into_iter()
            .filter(|e| matches!(e, ValidationError::FuncAttrClaimViolated { .. }))
            .count()
    };
    // A readonly caller dropping through a readonly glue: admitted.
    let mut m = with_table();
    m.functions[0].attrs.readonly = true;
    let caller = add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0))]);
    m.functions[caller.index() as usize].attrs.readonly = true;
    assert_eq!(claim_errors(&m), 0, "{:?}", validate_module(&m));
    // The glue carries no claim: the call edge violates the caller's.
    let mut m = with_table();
    let caller = add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0))]);
    m.functions[caller.index() as usize].attrs.readonly = true;
    assert_eq!(claim_errors(&m), 1);
    // Unresolved: an unstated destructor, refused under any claim.
    let mut m = base();
    m.functions[0].attrs.readonly = true;
    let caller = add_caller(&mut m, Ty::Ptr, vec![drop_node(s(0))]);
    m.functions[caller.index() as usize].attrs.readonly = true;
    assert_eq!(claim_errors(&m), 1);
}

/// The producer-side resolution rewrite (§20 rule 3; Lean:
/// `stepNWithContext_resolveDrops`): rewriting every resolved `Drop` to `Call
/// glue(ptr)` and `DropInvoke` to `Invoke glue(ptr)`, with the table then
/// REMOVED, preserves validity and the reference interpreter's verdict — a
/// drop IS a call of its glue, and nothing more.
#[test]
fn resolving_drops_to_calls_preserves_validity_and_interpretation() {
    use trust_ir::{InterpretValue, Interpreter};
    // A glue that adds 1 to the `i64` at its place; `run() -> i64` drops
    // through it twice (plain, then through a DropInvoke) over a cell
    // holding 40.
    let mut m = base();
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty: Ty::I64,
            lhs: v(1),
            rhs: v(2),
        })
        .with_result(v(3)),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(3),
            volatile: false,
            align: None,
        }),
        ret(),
    ];
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut run = Function::new(FuncId::new(2), "run", sig, b(0));
    let mut entry = Block::new(b(0));
    entry.body = vec![
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        })
        .with_result(v(0)),
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(40),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }),
        drop_node(s(0)),
        InstrNode::new(Inst::DropInvoke {
            ty: s(0),
            ptr: v(0),
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        }),
    ];
    run.blocks.push(entry);
    let mut normal = Block::new(b(1));
    normal.body = vec![
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_result(v(4)),
        InstrNode::new(Inst::Return { values: vec![v(4)] }),
    ];
    run.blocks.push(normal);
    let mut pad = Block::new(b(2));
    pad.body = vec![
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![v(5), v(6)]),
        InstrNode::new(Inst::Resume { exn: v(5) }),
    ];
    run.blocks.push(pad);
    m.try_add_function(run)
        .expect("Module::try_add_function: test fixture");

    // The rewrite: resolve through the table, then drop the table.
    let mut rewritten = m.clone();
    let index = rewritten.drop_glue_index();
    for function in &mut rewritten.functions {
        for block in &mut function.blocks {
            for node in &mut block.body {
                let resolved = match &node.inst {
                    Inst::Drop { ty, ptr } => match index.resolve(ty) {
                        trust_ir::DropResolution::Resolved(glue) => Some(Inst::Call {
                            callee: glue,
                            args: vec![*ptr],
                        }),
                        _ => None,
                    },
                    Inst::DropInvoke {
                        ty,
                        ptr,
                        normal_dest,
                        normal_args,
                        unwind_dest,
                    } => match index.resolve(ty) {
                        trust_ir::DropResolution::Resolved(glue) => Some(Inst::Invoke {
                            callee: glue,
                            args: vec![*ptr],
                            normal_dest: *normal_dest,
                            normal_args: normal_args.clone(),
                            unwind_dest: *unwind_dest,
                        }),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(inst) = resolved {
                    node.inst = inst;
                }
            }
        }
    }
    rewritten.drop_glue.clear();
    assert!(
        rewritten
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.body)
            .all(|n| !matches!(n.inst, Inst::Drop { .. } | Inst::DropInvoke { .. })),
        "every drop resolved"
    );

    // §4 applied: both validate, and the interpreter's verdict is the same.
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(validate_module(&rewritten), vec![]);
    let before = Interpreter::with_module(&m)
        .execute_func(FuncId::new(2), [])
        .expect("the drops run their glue");
    let after = Interpreter::with_module(&rewritten)
        .execute_func(FuncId::new(2), [])
        .expect("the calls run the same glue");
    assert_eq!(before.returns, after.returns);
    assert_eq!(
        before.returns,
        vec![InterpretValue::int(Ty::I64, 42).unwrap()]
    );
    assert_eq!(before.steps, after.steps, "a drop costs exactly a call");
}
