// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS4.12 — the builder API doors.
//
// Before this increment a producer that needed an enum, record, closure type,
// import, spec module, `global_asm!` block, function linkage or function
// summary had to `build()` the module early and mutate its tables by hand, and
// the only per-instruction proof door was the `*_proven` emitter family. Every
// door added here is a thin pass-through: it must produce EXACTLY the module
// the hand-built spelling produces (the conformance generator's spelling in
// `trust-ir-conformance/tests/generate.rs`: `build_ty_composite`,
// `build_composition`, `build_ty_handle`, `build_body_gate`), and it must
// grant no claim — the validator stays the authority. The restated hand
// spellings below are pinned to the generator itself (`generate::build_*`,
// included by path), so a generator edit cannot leave them silently stale.
//
// Layout:
// * positive twins — door-built module `==` hand-built module, per door;
// * negative twins — `annotate_last` with nothing to annotate is refused with
//   the named `BuilderError::NoEmittedInstruction`, and writes nothing;
// * mutation control — the `annotate_last` mutant that writes to
//   `Function::proofs` instead of the node is caught by the positive twin's
//   own check;
// * authority — a `proved` bit set through `set_summary` is re-counted and
//   refused by the validator exactly as the hand-built spelling is.

use trust_ir::inst::{BinOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::proof::{ProofAnnotation, ProofDigest};
use trust_ir::spec::{SpecInvariant, SpecModule, SpecVar};
use trust_ir::ty::{ClosureTy, EnumDef, EnumTagRepr, EnumVariant, FieldDef, FuncTy, RecordDef};
use trust_ir::ty::{StructDef, Ty};
use trust_ir::value::{BlockId, EnumId, FuncId, ProofId, RecordId, StructId, ValueId};
use trust_ir::{
    Block, Endianness, ExternRef, Function, FunctionSummary, Linkage, Module, ModuleImport,
    Producer, ProofFormula, TargetInfo,
};
use trust_ir_build::{BuilderError, ModuleBuilder, ValidationError, validate_module};

// The conformance generator, by path: the positive twins compare against the
// modules it ACTUALLY builds (the golden bytes' source), not only against a
// restatement that could drift from it.
#[path = "../../trust-ir-conformance/tests/generate.rs"]
#[allow(dead_code)]
mod generate;

#[test]
fn typed_call_boundary_fixture_needs_no_binary_builder_feature() {
    let module = generate::build_call_unwind_boundary().expect("call boundary fixture builds");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
}

// ── shared rows (verbatim from the conformance generator) ──────────────────

fn point_struct() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "Point".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::F64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    }
}

fn maybe_enum() -> EnumDef {
    EnumDef {
        id: EnumId::new(0),
        name: "Maybe".into(),
        variants: vec![
            EnumVariant {
                name: "Some".into(),
                fields: vec![Ty::I64],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
        origin: None,
    }
}

fn sparse_enum() -> EnumDef {
    EnumDef::new(
        EnumId::new(1),
        "Sparse",
        vec![
            EnumVariant {
                name: "Neg".into(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Next".into(),
                fields: vec![Ty::I16],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Big".into(),
                fields: vec![],
                field_names: Vec::new(),
            },
        ],
    )
    .with_discriminants(vec![Some(-3), None, Some(1000)])
    .with_repr(EnumTagRepr::I16)
}

fn vec2_record() -> RecordDef {
    RecordDef {
        id: RecordId::new(0),
        name: "Vec2".into(),
        fields: vec![
            FieldDef {
                name: "x".into(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "y".into(),
                ty: Ty::I64,
                offset: None,
            },
        ],
    }
}

fn i32_to_i32() -> FuncTy {
    FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        abi: None,
        is_vararg: false,
    }
}

fn aarch64() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    }
}

fn prelude_import() -> ModuleImport {
    // The frozen `composition` golden's row: a legacy V2 (pre-v44) record.
    ModuleImport::new("trusted_prelude", ProofDigest::sha256([0x11; 32]))
        .with_producer(Producer::Clean)
        .with_scheme(trust_ir::IdentityScheme::V2)
}

fn reciprocal_summary(prelude: trust_ir::value::ImportId) -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .requiring(ProofFormula::trust_types_json(
            "{\"Ne\":[{\"Var\":[\"x\",\"Int\"]},{\"Int\":0}]}",
            "(not (= x 0))",
            "Bool",
        ))
        .ensuring(ProofFormula::smtlib2("(not (= result 0))", "Bool"))
        .backed_by(ExternRef::new(prelude, "reciprocal").relying_on(ProofId::new(3)))
        .proved()
}

fn passthrough_summary() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(ProofFormula::smtlib2("(= result x)", "Bool"))
}

// ── the empty baseline ─────────────────────────────────────────────────────

/// Every positive twin below compares a `ModuleBuilder` build against a
/// `Module::new` build, so first pin that the two empty spellings agree.
#[test]
fn empty_builder_module_equals_empty_hand_module() {
    assert_eq!(
        ModuleBuilder::new("m")
            .build()
            .expect("ModuleBuilder::build: test fixture"),
        Module::new("m")
    );
}

// ── add_enum / add_record / add_closure_type (build_ty_composite) ──────────

/// The side tables `build_ty_composite` fills by hand, filled through the
/// doors: same rows, same returned ids, same module.
#[test]
fn door_enum_record_closure_tables_equal_hand_built_ty_composite() {
    // Hand spelling: the generator's own sequence of `Module` calls.
    let mut hand = Module::new("ty_composite");
    let h_point = hand.add_struct(point_struct());
    let h_maybe = hand.add_enum(maybe_enum());
    let h_sparse = hand.add_enum(sparse_enum());
    let h_rec = hand.add_record(vec2_record());
    let h_ft = hand
        .add_func_type(i32_to_i32())
        .expect("Module::add_func_type: test fixture");
    let h_closure = hand
        .add_closure_type(ClosureTy {
            func: h_ft,
            captures: vec![Ty::I64, Ty::F64],
        })
        .expect("Module::add_closure_type: test fixture");
    let h_i32 = hand
        .add_type(Ty::I32)
        .expect("Module::add_type: test fixture");

    // Door spelling.
    let mut mb = ModuleBuilder::new("ty_composite");
    let d_point = mb.add_struct(point_struct());
    let d_maybe = mb.add_enum(maybe_enum());
    let d_sparse = mb.add_enum(sparse_enum());
    let d_rec = mb.add_record(vec2_record());
    let d_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let d_closure = mb.add_closure_type(ClosureTy {
        func: d_ft,
        captures: vec![Ty::I64, Ty::F64],
    });
    let d_i32 = mb.add_type(Ty::I32);
    let door = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(
        (d_point, d_maybe, d_sparse, d_rec, d_ft, d_closure, d_i32),
        (h_point, h_maybe, h_sparse, h_rec, h_ft, h_closure, h_i32)
    );
    assert_eq!(door.enums.len(), 2);
    assert_eq!(door.records.len(), 1);
    assert_eq!(door.closure_types.len(), 1);
    assert_eq!(door, hand);

    // The generator's own tables, row for row (its function and globals are
    // hand-numbered and out of scope for the doors).
    let generated = generate::build_ty_composite().expect("the fixture builds");
    assert_eq!(door.structs, generated.structs);
    assert_eq!(door.enums, generated.enums);
    assert_eq!(door.records, generated.records);
    assert_eq!(door.closure_types, generated.closure_types);
    assert_eq!(door.types, generated.types);
    assert_eq!(
        door.func_types[..],
        generated.func_types[..door.func_types.len()]
    );
}

/// `add_enum` is the RAW pass-through, like `add_struct`: it does not dedup
/// and does not police the id space. A colliding id is the validator's to
/// refuse, and the door must not quietly repair it.
#[test]
fn door_add_enum_is_raw_and_leaves_collisions_to_the_validator() {
    let mut mb = ModuleBuilder::new("collide");
    assert_eq!(mb.add_enum(maybe_enum()), EnumId::new(0));
    assert_eq!(mb.add_enum(maybe_enum()), EnumId::new(0));
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(m.enums.len(), 2, "the door must append, not dedup");
    assert!(
        !validate_module(&m).is_empty(),
        "two defs sharing EnumId 0 must still be refused by the validator"
    );
}

// ── intern_func_type ───────────────────────────────────────────────────────

#[test]
fn door_intern_func_type_is_structural_and_idempotent() {
    let mut mb = ModuleBuilder::new("intern_ft");
    let a = mb.intern_func_type(i32_to_i32());
    let b = mb.intern_func_type(i32_to_i32());
    assert_eq!(a, b, "a structurally equal signature reuses its row");

    // Every field is identity: vararg-ness distinguishes two signatures.
    let va = mb.intern_func_type(FuncTy {
        is_vararg: true,
        ..i32_to_i32()
    });
    assert_ne!(a, va);

    // `add_func_type` stays the always-appending constructor.
    let appended = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    assert_ne!(appended, a);
    // ...and interning after that still finds the FIRST equal row.
    assert_eq!(mb.intern_func_type(i32_to_i32()), a);

    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(m.func_types.len(), 3);

    let mut hand = Module::new("intern_ft");
    hand.add_func_type(i32_to_i32())
        .expect("Module::add_func_type: test fixture");
    hand.add_func_type(FuncTy {
        is_vararg: true,
        ..i32_to_i32()
    })
    .expect("Module::add_func_type: test fixture");
    hand.add_func_type(i32_to_i32())
        .expect("Module::add_func_type: test fixture");
    assert_eq!(m, hand);
}

// ── intern_import + set_summary (build_composition) ────────────────────────

/// The generator's hand-built `composition` module, restated verbatim.
fn hand_composition() -> Module {
    let mut module = Module::new("composition");
    module.target_info = Some(aarch64());
    let prelude = module
        .intern_import(prelude_import())
        .expect("Module::intern_import: test fixture");
    let ft = module
        .add_func_type(i32_to_i32())
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(Function::declaration(
            FuncId::new(0),
            "reciprocal",
            ft,
            reciprocal_summary(prelude),
        ))
        .expect("Module::try_add_function: test fixture");
    let mut caller = Function::new(FuncId::new(1), "passthrough", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::I32));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    caller.blocks.push(block);
    caller.summary = Some(passthrough_summary());
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn door_import_and_summary_equal_hand_built_composition() {
    let mut mb = ModuleBuilder::new_with_target_info("composition", aarch64());
    let prelude = mb.intern_import(prelude_import());
    // Interning is idempotent: a second citation of the same artifact reuses
    // the row rather than minting a second, distinct-looking dependency.
    assert_eq!(mb.intern_import(prelude_import()), prelude);
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // A body-less function whose only content is its contract.
    let mut fb = mb.function("reciprocal", ft);
    fb.set_summary(reciprocal_summary(prelude));
    fb.build();

    let mut fb = mb.function("passthrough", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.set_summary(passthrough_summary());
    fb.build();

    let door = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(door.imports.len(), 1);
    assert_eq!(door, hand_composition());
    assert_eq!(
        door,
        generate::build_composition().expect("the fixture builds")
    );
    assert_eq!(validate_module(&door), validate_module(&hand_composition()));
}

#[test]
fn door_clear_summary_restores_no_contract() {
    let mut mb = ModuleBuilder::new("clear");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    fb.set_summary(passthrough_summary());
    fb.clear_summary();
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(m.functions[0].summary, None);
}

/// The door grants nothing: an unbacked `proved` bit on a DEFINITION, set
/// through `set_summary`, is refused by the validator exactly as the
/// hand-built spelling is — the builder did not certify it on the way in.
#[test]
fn door_set_summary_proved_is_still_recounted_by_the_validator() {
    let build = |via_door: bool| {
        let mut mb = ModuleBuilder::new("unbacked");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        if via_door {
            fb.set_summary(passthrough_summary().proved());
        }
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        if !via_door {
            m.functions[0].summary = Some(passthrough_summary().proved());
        }
        m
    };
    let (door, hand) = (build(true), build(false));
    assert_eq!(door, hand);

    // WS1.3: `proved` is per-clause, so the refusal names the unbacked clause.
    let errors = validate_module(&door);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidFunctionSummary { function: 0, detail }
                if detail.starts_with(
                    "ensures clause 0 `(= result x)` has no Discharged/Certified \
                     Postcondition row scoped to this function"
                )
        )),
        "an unbacked `proved` must be refused as InvalidFunctionSummary, got {errors:?}"
    );
    assert_eq!(errors, validate_module(&hand));
}

// ── the whole-builder flow (build_ty_handle) ───────────────────────────────

/// `build_ty_handle` calls `mb.build()` early and hand-assembles `pred`
/// (`FuncId` 4, after the four pinned declarations). With the doors, nothing
/// forces that: the same module comes out of one uninterrupted builder flow.
#[test]
fn door_flow_equals_hand_built_ty_handle() {
    let pin = trust_ir_build::TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("the v1 Nat row is pinned");
    let roles = ["from_u64", "add", "sub", "is_zero"];

    // Hand spelling, restated from the generator.
    let hand = {
        let mut mb = ModuleBuilder::new_with_target_info("ty_handle_v43", aarch64());
        let decls = mb
            .declare_handle_runtime_roles(pin, &roles)
            .expect("fresh module");
        let h = decls.handle.clone();
        let (from_u64, sub, is_zero) = (
            decls.entry("from_u64").unwrap(),
            decls.entry("sub").unwrap(),
            decls.entry("is_zero").unwrap(),
        );
        let unop = mb.add_func_type(vec![h.clone()], vec![h.clone()]);
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        let mut pred = Function::new(FuncId::new(4), "pred", unop, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.params.push((ValueId::new(0), h));
        entry.body.push(
            InstrNode::new(Inst::Call {
                callee: is_zero,
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
        );
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: ValueId::new(1),
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }));
        let mut zero = Block::new(BlockId::new(1));
        zero.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        let mut step = Block::new(BlockId::new(2));
        step.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: trust_ir::constant::Constant::Int(1),
            })
            .with_result(ValueId::new(2)),
        );
        step.body.push(
            InstrNode::new(Inst::Call {
                callee: from_u64,
                args: vec![ValueId::new(2)],
            })
            .with_result(ValueId::new(3)),
        );
        step.body.push(
            InstrNode::new(Inst::Call {
                callee: sub,
                args: vec![ValueId::new(0), ValueId::new(3)],
            })
            .with_result(ValueId::new(4)),
        );
        step.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(4)],
        }));
        pred.blocks = vec![entry, zero, step];
        pred.body_gate = Some(trust_ir::BodyGate::Gated {
            authority: "conformance-fixture".into(),
            evidence: None,
        });
        m.try_add_function(pred)
            .expect("Module::try_add_function: test fixture");
        m
    };

    // Door spelling: the builder never lets go of the module.
    let mut mb = ModuleBuilder::new_with_target_info("ty_handle_v43", aarch64());
    let decls = mb
        .declare_handle_runtime_roles(pin, &roles)
        .expect("fresh module");
    let h = decls.handle.clone();
    let (from_u64, sub, is_zero) = (
        decls.entry("from_u64").unwrap(),
        decls.entry("sub").unwrap(),
        decls.entry("is_zero").unwrap(),
    );
    let unop = mb.add_func_type(vec![h.clone()], vec![h.clone()]);
    let mut fb = mb.function("pred", unop);
    let entry = fb.create_block();
    let zero = fb.create_block();
    let step = fb.create_block();
    let n = fb.add_block_param(entry, h);
    fb.switch_to_block(entry);
    let done = fb.call(is_zero, vec![n]);
    fb.condbr(done, zero, vec![], step, vec![]);
    fb.switch_to_block(zero);
    fb.ret(vec![n]);
    fb.switch_to_block(step);
    let one = fb.iconst(Ty::U64, 1);
    let one = fb.call(from_u64, vec![one]);
    let prev = fb.call(sub, vec![n, one]);
    fb.ret(vec![prev]);
    fb.set_body_gate(trust_ir::BodyGate::Gated {
        authority: "conformance-fixture".into(),
        evidence: None,
    });
    fb.build();
    let door = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(door, hand);
    assert_eq!(
        door,
        generate::build_ty_handle().expect("the fixture builds")
    );
    assert_eq!(validate_module(&door), validate_module(&hand));
}

// ── set_linkage + FunctionSummary::decreasing ──────────────────────────────

#[test]
fn door_set_linkage_equals_hand_set_linkage() {
    for linkage in [
        Linkage::Internal,
        Linkage::External,
        Linkage::LinkOnceOdr,
        Linkage::ExternalWeak,
    ] {
        let build = |via_door: bool| {
            let mut mb = ModuleBuilder::new("linkage");
            let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, Ty::I32);
            fb.switch_to_block(entry);
            fb.ret(vec![x]);
            if via_door {
                fb.set_linkage(linkage);
            }
            fb.build();
            let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
            if !via_door {
                m.functions[0].linkage = linkage;
            }
            m
        };
        let door = build(true);
        assert_eq!(door.functions[0].linkage, linkage);
        assert_eq!(door, build(false));
    }
}

#[test]
fn decreasing_appends_a_measure_and_claims_nothing() {
    let measure = ProofFormula::smtlib2("n", "Int");
    let second = ProofFormula::smtlib2("m", "Int");
    let s = FunctionSummary::new()
        .with_params(vec!["n".into(), "m".into()])
        .decreasing(measure.clone())
        .decreasing(second.clone());
    assert_eq!(s.decreases, vec![measure.clone(), second.clone()]);
    assert!(!s.proved, "recording a measure must not set `proved`");

    let mut hand = FunctionSummary::new().with_params(vec!["n".into(), "m".into()]);
    hand.decreases.push(measure);
    hand.decreases.push(second);
    assert_eq!(s, hand);
}

// ── add_spec_module + add_global_asm ───────────────────────────────────────

fn counter_spec() -> SpecModule {
    let mut spec = SpecModule::new("Counter");
    spec.vars.push(SpecVar::new("count", "Nat"));
    spec.actions.push("Incr".into());
    spec.invariants
        .push(SpecInvariant::new("NonNeg", "count >= 0"));
    spec
}

#[test]
fn door_spec_module_and_global_asm_equal_hand_pushes() {
    let mut mb = ModuleBuilder::new("spec_asm");
    mb.add_spec_module(counter_spec());
    mb.add_global_asm(".globl _marker");
    mb.add_global_asm(String::from("_marker: ret"));
    let door = mb.build().expect("ModuleBuilder::build: test fixture");

    let mut hand = Module::new("spec_asm");
    hand.spec_modules.push(counter_spec());
    hand.global_asm.push(".globl _marker".into());
    hand.global_asm.push("_marker: ret".into());

    assert_eq!(door.global_asm, vec![".globl _marker", "_marker: ret"]);
    assert_eq!(door, hand);
}

// ── add_function_proof / deprecated add_proof ──────────────────────────────

#[test]
fn add_function_proof_writes_function_level_like_build_body_gate_spelling() {
    let build = |which: u8| {
        let mut mb = ModuleBuilder::new("fn_proof");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        match which {
            0 => fb.add_function_proof(ProofAnnotation::Pure),
            #[allow(deprecated)]
            1 => fb.add_proof(ProofAnnotation::Pure),
            _ => {}
        }
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        if which == 2 {
            m.functions[0].proofs.push(ProofAnnotation::Pure);
        }
        m
    };
    let door = build(0);
    assert_eq!(door.functions[0].proofs, vec![ProofAnnotation::Pure]);
    assert!(
        door.functions[0].blocks[0]
            .body
            .iter()
            .all(|n| n.proofs.is_empty())
    );
    // The deprecated alias is exactly the function-level door.
    assert_eq!(build(1), door);
    assert_eq!(build(2), door);
}

// ── annotate_last: positive twin, negative twins, mutation control ─────────

/// The positive twin's check, factored out so the mutation control can run it
/// against a mutant: the annotation sits on the `add` node and NOWHERE else.
fn check_annotation_on_add_node(m: &Module) -> Result<(), String> {
    let f = &m.functions[0];
    if !f.proofs.is_empty() {
        return Err(format!(
            "function-level proofs must stay empty, found {:?}",
            f.proofs
        ));
    }
    let body = &f.blocks[0].body;
    let add = body
        .iter()
        .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Add, .. }))
        .ok_or("no add node")?;
    if add.proofs != vec![ProofAnnotation::NoOverflow] {
        return Err(format!(
            "add node must carry exactly [NoOverflow], found {:?}",
            add.proofs
        ));
    }
    let stray = body
        .iter()
        .filter(|n| !matches!(n.inst, Inst::BinOp { op: BinOp::Add, .. }))
        .any(|n| !n.proofs.is_empty());
    if stray {
        return Err("an annotation landed on a node other than the add".into());
    }
    Ok(())
}

/// Build `f(x) = x + 1` and annotate the add through `annotate`.
fn build_add_one(annotate: impl FnOnce(&mut trust_ir_build::FunctionBuilder<'_>)) -> Module {
    let mut mb = ModuleBuilder::new("annotate_last");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("add_one", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::I32, 1);
    let sum = fb.binop(BinOp::Add, Ty::I32, x, one);
    annotate(&mut fb);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn annotate_last_attaches_to_the_last_emitted_node() {
    let door = build_add_one(|fb| {
        let pos = fb.last_emitted_position();
        fb.annotate_last(ProofAnnotation::NoOverflow)
            .expect("a node was just emitted");
        // The door did not move the cursor or emit anything.
        assert_eq!(fb.last_emitted_position(), pos);
    });
    check_annotation_on_add_node(&door).expect("positive twin");

    // Equal to the hand-built spelling: push onto the node's own proofs.
    let mut hand = build_add_one(|_| {});
    let add = hand.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Add, .. }))
        .unwrap();
    add.proofs.push(ProofAnnotation::NoOverflow);
    assert_eq!(door, hand);
}

/// Mutation control: the `annotate_last` mutant that widens the claim to the
/// whole function (writes `Function::proofs`) must fail the positive twin's
/// check. If this ever passes, the positive twin is not testing placement.
#[test]
fn annotate_last_mutant_writing_function_proofs_is_caught() {
    let mutant = build_add_one(|fb| fb.add_function_proof(ProofAnnotation::NoOverflow));
    let err = check_annotation_on_add_node(&mutant)
        .expect_err("a function-level write must fail the node-level check");
    assert!(err.contains("function-level"), "{err}");

    // And the mutant that annotates the WRONG node (the constant before it).
    let mut wrong_node = build_add_one(|_| {});
    let konst = wrong_node.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|n| matches!(n.inst, Inst::Const { .. }))
        .unwrap();
    konst.proofs.push(ProofAnnotation::NoOverflow);
    assert!(check_annotation_on_add_node(&wrong_node).is_err());
}

/// Negative twin: at the start of a FRESH block there is no node to annotate.
/// The door refuses with the named reason carrying that block, and writes
/// nothing — in particular it does not fall back to `Function::proofs`.
#[test]
fn annotate_last_on_a_fresh_block_is_refused() {
    let mut mb = ModuleBuilder::new("fresh");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    let next = fb.create_block();
    fb.switch_to_block(entry);
    let _ = fb.iconst(Ty::I32, 7);
    fb.br(next, vec![]);
    fb.switch_to_block(next);

    assert_eq!(
        fb.annotate_last(ProofAnnotation::NoOverflow),
        Err(BuilderError::NoEmittedInstruction { block: Some(next) })
    );
    fb.ret(vec![x]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    let f = &m.functions[0];
    assert!(
        f.proofs.is_empty(),
        "refusal must not widen to the function"
    );
    assert!(
        f.blocks
            .iter()
            .flat_map(|b| &b.body)
            .all(|n| n.proofs.is_empty()),
        "refusal must not reach back into the previous block's last node"
    );
}

/// Negative twin: no block selected at all.
#[test]
fn annotate_last_with_no_selected_block_is_refused() {
    let mut mb = ModuleBuilder::new("unselected");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let err = fb
        .annotate_last(ProofAnnotation::NoPanic)
        .expect_err("no block is selected");
    assert_eq!(err, BuilderError::NoEmittedInstruction { block: None });
    assert!(!err.to_string().is_empty());
    fb.build();
    assert!(
        mb.build()
            .expect("ModuleBuilder::build: test fixture")
            .functions[0]
            .proofs
            .is_empty()
    );
}

/// The door records a claim and checks nothing: annotating a node with an
/// annotation the validator does not admit there is not refused by the
/// builder, and the validator still sees (and judges) exactly what the
/// hand-built spelling would have produced.
#[test]
fn annotate_last_checks_nothing_the_validator_judges() {
    let weights = ProofAnnotation::BranchWeights(vec![1, 2]);
    let door = build_add_one(|fb| {
        fb.annotate_last(weights.clone())
            .expect("the builder records claims unchecked");
    });
    let mut hand = build_add_one(|_| {});
    hand.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Add, .. }))
        .unwrap()
        .proofs
        .push(weights);
    assert_eq!(door, hand);
    // BranchWeights on a non-terminator is a placement error.
    assert!(!validate_module(&door).is_empty());
    assert_eq!(validate_module(&door), validate_module(&hand));
}

// ── adversarial review (WS4.12) ────────────────────────────────────────────

/// Stale cursor: emit into A, emit into B, switch BACK to A and annotate. The
/// instruction just emitted is B's, but A's last node is what
/// `last_emitted_position` names — attaching there would put the claim on an
/// instruction the producer did not just emit. The door must refuse, not
/// guess, and write nothing.
#[test]
fn annotate_last_after_switching_back_to_an_older_block_is_refused() {
    let mut mb = ModuleBuilder::new("stale_cursor");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let a = fb.create_block();
    let x = fb.add_block_param(a, Ty::I32);
    let b = fb.create_block();
    let y = fb.add_block_param(b, Ty::I32);
    fb.switch_to_block(a);
    let one = fb.iconst(Ty::I32, 1);
    let sum = fb.add(Ty::I32, x, one);
    fb.switch_to_block(b);
    let two = fb.iconst(Ty::I32, 2);
    let _prod = fb.mul(Ty::I32, y, two);
    fb.switch_to_block(a);

    assert_eq!(
        fb.annotate_last(ProofAnnotation::NoOverflow),
        Err(BuilderError::LastEmittedInAnotherBlock {
            block: a,
            emitted_in: b,
        })
    );

    // Re-selecting the block that DOES hold the last emitted node is fine,
    // and so is re-selecting the current block (a no-op switch).
    fb.switch_to_block(b);
    fb.switch_to_block(b);
    fb.annotate_last(ProofAnnotation::NoOverflow)
        .expect("b's last node is the instruction just emitted");
    fb.ret(vec![sum]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    let f = &m.functions[0];
    assert!(f.proofs.is_empty());
    assert!(
        f.blocks[0].body.iter().all(|n| n.proofs.is_empty()),
        "the refused call must not have written into block a"
    );
    let mul = f.blocks[1]
        .body
        .iter()
        .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Mul, .. }))
        .unwrap();
    assert_eq!(mul.proofs, vec![ProofAnnotation::NoOverflow]);
}

/// The two-phase path (`declare_function` → `define_function`) commits the
/// draft into the reserved slot rather than appending; the linkage and summary
/// doors must survive THAT commit too, and produce the module the hand
/// spelling (mutate the committed slot) produces.
#[test]
fn doors_survive_the_two_phase_definition_commit() {
    let build = |via_door: bool| {
        let mut mb = ModuleBuilder::new("two_phase");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let id = mb.declare_function("f", ft);
        // A caller built against the declaration before it is defined.
        let mut caller = mb.function("caller", ft);
        let entry = caller.create_block();
        let x = caller.add_block_param(entry, Ty::I32);
        caller.switch_to_block(entry);
        let r = caller.call(id, vec![x]);
        caller.ret(vec![r]);
        caller.build();

        let mut fb = mb.define_function(id).expect("reserved");
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        if via_door {
            fb.set_linkage(Linkage::Internal);
            fb.set_summary(passthrough_summary());
        }
        assert_eq!(fb.build(), id);
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        if !via_door {
            let slot = m.functions.iter().position(|f| f.id == id).unwrap();
            m.functions[slot].linkage = Linkage::Internal;
            m.functions[slot].summary = Some(passthrough_summary());
        }
        m
    };
    let door = build(true);
    let f = door.functions.iter().find(|f| f.name == "f").unwrap();
    assert_eq!(f.linkage, Linkage::Internal);
    assert_eq!(f.summary, Some(passthrough_summary()));
    assert_eq!(door.functions.len(), 2, "committed in place, not appended");
    assert_eq!(door, build(false));
    assert_eq!(validate_module(&door), validate_module(&build(false)));
}

/// `decreasing` records a measure and claims nothing: a `proved` summary that
/// gains a measure through it now needs a Discharged/Certified `Termination`
/// obligation, and without one the validator refuses it by name. The twin
/// without the measure is not refused on that ground.
#[test]
fn decreasing_measure_on_a_proved_summary_needs_a_termination_obligation() {
    let build = |measure: bool| {
        let mut mb = ModuleBuilder::new("measured");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        let mut summary = FunctionSummary::new().with_params(vec!["n".into()]);
        if measure {
            summary = summary.decreasing(ProofFormula::smtlib2("n", "Int"));
        }
        fb.set_summary(summary.proved());
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let unbacked_termination = |errors: &[ValidationError]| {
        errors.iter().any(|e| {
            matches!(
                e,
                ValidationError::InvalidFunctionSummary { function: 0, detail }
                    if detail.contains("decreases") && detail.contains("Termination")
            )
        })
    };
    let with = validate_module(&build(true));
    assert!(
        unbacked_termination(&with),
        "an unbacked measure under `proved` must be refused, got {with:?}"
    );
    let without = validate_module(&build(false));
    assert!(
        !unbacked_termination(&without),
        "no measure, no Termination debt: {without:?}"
    );
}

/// Interning is by STRUCTURE, and structure is nominal where the type system
/// is: a `Handle` is never `Ptr` (one pointer word, NOT pointer-like), and two
/// struct ids are two types even when their defs agree field for field.
/// Merging either pair would silently retype every function citing the row.
#[test]
fn intern_func_type_never_merges_nominally_distinct_signatures() {
    let mut mb = ModuleBuilder::new("nominal");
    let pin = trust_ir_build::TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("the v1 Nat row is pinned");
    let handle = Ty::Handle(Box::new(trust_ir::ty::HandleTy {
        name: pin.name.to_string(),
        runtime: pin.runtime.to_string(),
    }));
    let unary = |t: Ty| FuncTy {
        params: vec![t.clone()],
        returns: vec![t],
        abi: None,
        is_vararg: false,
    };
    let ptr = mb.intern_func_type(unary(Ty::Ptr));
    let h = mb.intern_func_type(unary(handle.clone()));
    assert_ne!(ptr, h, "a handle signature must not intern onto a Ptr one");
    let mut twin = point_struct();
    twin.id = StructId::new(1);
    mb.add_struct(point_struct());
    mb.add_struct(twin);
    let s0 = mb.intern_func_type(unary(Ty::Struct(StructId::new(0))));
    let s1 = mb.intern_func_type(unary(Ty::Struct(StructId::new(1))));
    assert_ne!(s0, s1, "struct identity is the id, not the field list");
    // ...and each is still idempotent on its own.
    assert_eq!(mb.intern_func_type(unary(handle)), h);
    assert_eq!(mb.intern_func_type(unary(Ty::Struct(StructId::new(1)))), s1);
    assert_eq!(
        mb.build()
            .expect("ModuleBuilder::build: test fixture")
            .func_types
            .len(),
        4
    );
}

/// The fixed context is public preprocessing for an ordinary non-TLA consumer.
/// A well-typed false claim can be materialized, but still has to earn replay.
#[test]
fn scoped_materialization_context_is_preprocessing_for_external_consumers() {
    use trust_ir_build::clean_kernel::{Environment, Expr, Level, Name, TypeChecker};
    use trust_ir_build::proof_assembly::ProofLimits;
    use trust_ir_build::proof_components::{
        OwnedProofCapture, ProofComponents, ScopedMaterializationContext,
        ScopedProofComponentBundle,
    };
    use trust_ir_build::scoped_local::LocalScope;
    use trust_ir_build::term_scope::TermScopeLimits;

    let mut environment = Environment::new();
    environment.init_nat().unwrap();
    environment.init_eq().unwrap();
    for false_claim in [false, true] {
        let nat = Expr::const_str("Nat");
        let mut scope = LocalScope::new();
        let input = scope.try_local(nat.clone()).unwrap();
        let mut parts = ProofComponents::new(
            "external.materialization.consumer",
            ProofLimits {
                operations: 100_000,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        parts
            .extend_base(OwnedProofCapture::Parameter(input.clone()))
            .unwrap();
        let original_value = Expr::nat_lit(7);
        let unused = parts
            .bind_scoped_owned(&mut scope, &[], nat.clone(), original_value.clone())
            .unwrap();
        let right = if false_claim {
            Expr::nat_lit(0)
        } else {
            input.term().clone()
        };
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat.clone(), input.term().clone(), right],
        );
        // The explicit external type and both method calls must be available
        // from the ordinary non-test library compiled for this integration test.
        let context: ScopedMaterializationContext = parts
            .prepare_scoped_materialization_context(&scope, std::slice::from_ref(&input))
            .unwrap();
        let candidates = parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&goal))
            .unwrap();
        assert_eq!(candidates, vec![goal.clone()]);
        let candidate = candidates.into_iter().next().unwrap();
        let claim = scope.close(&input.pi(candidate.clone())).unwrap();
        // The same reflexivity proof proves the positive goal, but cannot
        // prove the false forall x : Nat, x = 0 claim in the negative control.
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [nat.clone(), input.term().clone()],
        );
        let bundle = parts
            .close_scoped(
                &scope,
                input.lam(proof),
                candidate,
                TermScopeLimits::default(),
            )
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        assert_eq!(transported, claim);
        assert_eq!(decoded.outer_count, 1);
        assert_eq!(decoded.declarations.len(), 2);
        assert!(
            decoded.declarations.iter().any(|declaration| {
                declaration.id == unused.local.id()
                    && declaration.type_ == nat
                    && declaration.value.as_ref() == Some(&original_value)
            }),
            "the original valid unused Nat 7 definition must survive the wire"
        );
        // Both transported claims are well-typed propositions. The negative
        // control differs only in its semantic claim, never in its inventory.
        let mut checker = TypeChecker::new(&environment);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker.set_heartbeat_limit(1_000_000);
        checker.set_max_cache_entries(100_000);
        checker.check_type(&transported, &Expr::prop()).unwrap();
        assert!(!checker.heartbeat_spent());
        let replay = decoded.replay(&environment, &transported, 2_000_000);
        if false_claim {
            let error = replay
                .err()
                .expect("materializing a well-typed false goal grants no proof authority");
            assert!(error.contains("TypeMismatch"), "{error}");
            assert!(
                !error.contains("BudgetExhausted") && !error.contains("HeartbeatExceeded"),
                "{error}"
            );
        } else {
            replay.unwrap();
        }
    }
}
