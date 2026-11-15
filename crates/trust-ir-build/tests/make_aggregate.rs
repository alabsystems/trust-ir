// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// WS3.5 (F-049, register-seed half) — `Inst::MakeAggregate`.
// ══════════════════════════════════════════════════════════════════════════
//
// Before this instruction `Inst::Const` was the ONLY register-level
// originator of an aggregate value, and no `Constant` inhabits `Rc<T>` /
// `&T` / `&mut T` / `*const T` / `*mut T` (a constant reference has no
// provenance — `shape::shape_matches_ty`). An enum or struct with a
// typed-reference lane therefore had no register seed at all: only the
// memory lane (`Alloca` / `HeapAlloc` + field `Store`s + `Load`) could
// originate one, and `Undef` + `InsertField` is no seed (it executes as UB).
// Proof-program row `b6.enum.typed_ref_payload_has_no_register_seed`
// (2026-09-17 two-language program, partb/tests/b6_data_carriers.rs) pinned
// that gap; its port in `trust-ir-conformance/tests/two_language/b6_*` is
// flipped to PASS by this increment, and this file is the validator-side
// battery behind the flip:
//
//   * positive — the `b6` boxed-tree program re-spelled with
//     `make_aggregate enum.0 variant 1 (%l1, %l2)` over `(Rc<Tree>, Rc<Tree>)`
//     validates, survives the licensed codegen entry point, and the reference
//     interpreter returns 42;
//   * negative twin — the old `Const [Int(1), Int(0), Int(0)]` seed stays
//     EXACTLY two `ConstTypeMismatch` (no constant rule is widened: a constant
//     `Rc` / `&mut` still has no provenance);
//   * mutation controls — lane order swapped (`(Rc, U64)` operands for a
//     `(U64, Rc)` struct) refused; enum arity off by one refused; variant
//     index = variant count refused; a `Ref(T)` operand for an `Rc(T)` lane
//     refused (EXACTNESS, not `is_pointer_like`); a `variant` clause on a
//     struct, no `variant` on an enum, a non-aggregate type, an uninhabited
//     variant, and an unrefined operand for a refined lane (the SAME
//     consumption rule `InsertField` applies) each refused by name.
//
// The instruction is total and statically typed: there is no run-time
// obligation, the validator rule IS the side condition, and the interpreter
// enforces the same shape so an unvalidated module fails closed there too.

use trust_ir::constant::Constant;
use trust_ir::inst::{AllocOrigin, CastOp, Inst, SwitchCase};
use trust_ir::interpret::{InterpretOptions, InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{
    EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumVariant, FieldDef, StructDef, StructRepr,
};
use trust_ir::value::{BlockId, EnumId, FuncId, StructId, ValueId};
use trust_ir::{Block, BodyGate, FuncTy, Function, Module, Pred, Producer, Space, Ty, Universe};
use trust_ir_build::{
    ModuleBuilder, ValidationError, validate_module, validate_module_for_codegen,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn run_nullary(module: &Module, entry: &str) -> Result<Vec<InterpretValue>, String> {
    let func = module
        .function_by_name(entry)
        .ok_or_else(|| format!("no function named @{entry}"))?;
    Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 50_000_000,
            max_call_depth: 4096,
            ..InterpretOptions::default()
        })
        .execute_func(func.id, Vec::new())
        .map(|outcome| outcome.returns)
        .map_err(|e| e.to_string())
}

fn run_u64(module: &Module, entry: &str) -> Option<u128> {
    run_nullary(module, entry)
        .ok()?
        .first()?
        .as_int()
        .map(|i| i.as_unsigned())
}

/// Every definition licensed, so the strictest entry point is meaningful.
///
/// The Clean bodies wear an authority the codegen layer binds to NO
/// evidence: since WS1.5, `clean-kernel-tv` demands a kernel-rechecked
/// `TranslationValidation` certificate per body
/// (`EVIDENCE_BOUND_GATE_AUTHORITIES`), which this register-seed fixture does
/// not mint — the same spelling the WS1.5-conformed `enum_lane_access` tree
/// wears. What this battery measures is the INSTRUCTION's standing at the
/// strictest entry point, not the license's.
fn license(m: &Module) -> Module {
    let mut m = m.clone();
    for f in &mut m.functions {
        if f.body_gate.is_none() && !f.blocks.is_empty() {
            let authority = if f.producer == Some(Producer::Clean) {
                "trust-direct-lane-structural"
            } else {
                "trust-verify"
            };
            f.body_gate = Some(BodyGate::Gated {
                authority: authority.into(),
                evidence: None,
            });
        }
    }
    m
}

fn invalid_make_aggregate(errors: &[ValidationError], needle: &str) -> bool {
    errors.iter().any(|e| {
        matches!(e, ValidationError::InvalidMakeAggregate { reason, .. } if reason.contains(needle))
    })
}

fn lane_mismatch(errors: &[ValidationError], lane: &str, expected: &str, actual: &str) -> bool {
    errors.iter().any(|e| {
        matches!(
            e,
            ValidationError::OperandTypeMismatch { op, role, expected: exp, actual: act, .. }
            if op == "make_aggregate" && role == lane && exp == expected && act == actual
        )
    })
}

fn assert_clean(module: &Module, what: &str) {
    let errors = validate_module(module);
    assert!(
        errors.is_empty(),
        "{what}: expected no errors, got {errors:?}"
    );
}

// ---------------------------------------------------------------------------
// The boxed tree: `inductive Tree | leaf (v : UInt64) | node (l r : Tree)`
// with the recursive fields TYPED `Rc<Tree>` (the b6 shape).
// ---------------------------------------------------------------------------

fn tree_def() -> EnumDef {
    let tree = Ty::Enum(EnumId::new(0));
    let rc = Ty::Rc(Box::new(tree));
    let mut def = EnumDef::new(
        EnumId::new(0),
        "Tree",
        vec![
            EnumVariant {
                name: "leaf".into(),
                fields: vec![Ty::U64],
                field_names: vec!["value".into()],
            },
            EnumVariant {
                name: "node".into(),
                fields: vec![rc.clone(), rc],
                field_names: vec!["left".into(), "right".into()],
            },
        ],
    );
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 16 },
        size: 24,
        align: 8,
        variant_field_offsets: vec![vec![0], vec![0, 8]],
    });
    def
}

/// How `program` seeds the `node` cell it stores into the Clean heap.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NodeSeed {
    /// `make_aggregate enum.0 variant 1 (%l1, %l2)` — the WS3.5 spelling.
    MakeAggregate,
    /// The pre-WS3.5 `Const [Int(1), Int(0), Int(0)]` + two `InsertField`s:
    /// the F-049 gap, which must STAY refused (no constant rule is widened).
    ConstSeed,
    /// Mutation: the payload arity is off by one (`(%l1)` for a 2-lane variant).
    ArityOffByOne,
    /// Mutation: `variant 2` on a 2-variant enum (index = count).
    VariantEqualsCount,
    /// Mutation: no `variant` clause on an enum construction.
    VariantMissing,
    /// Mutation: lane 1 is the bare `Ptr` cell, not the `Rc<Tree>` handle.
    PtrForRcLane,
    /// Mutation: lane 1 is a `&Tree`, not an `Rc<Tree>` — exactness, not
    /// `is_pointer_like`.
    RefForRcLane,
}

fn build_rc_tree(seed: NodeSeed) -> Module {
    let tree = Ty::Enum(EnumId::new(0));
    let rc = Ty::Rc(Box::new(tree.clone()));
    let mut mb = ModuleBuilder::new("ws3_5_rc_tree");
    let sum_ty = mb.add_func_type(vec![rc.clone()], vec![Ty::U64]);
    let mk_ty = mb.add_func_type(vec![Ty::U64], vec![rc.clone()]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let sum_id = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    {
        let mut fb = mb.function("clean_rc_tree_sum", sum_ty);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let leaf = fb.create_block();
        let node = fb.create_block();
        let dead = fb.create_block();
        let t = fb.add_block_param(entry, rc.clone());
        fb.switch_to_block(entry);
        let v = fb.load(tree.clone(), t);
        let tag = fb.extract_field(Ty::U8, v, 0);
        fb.switch(
            tag,
            vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: leaf,
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: node,
                    args: vec![],
                },
            ],
            dead,
            vec![],
        );
        fb.switch_to_block(leaf);
        let value = fb.extract_field(Ty::U64, v, 1);
        fb.ret(vec![value]);
        fb.switch_to_block(node);
        let l = fb.extract_field(rc.clone(), v, 1);
        let r = fb.extract_field(rc.clone(), v, 2);
        let a = fb.call(sum_id, vec![l]);
        let b = fb.call(sum_id, vec![r]);
        let s = fb.add(Ty::U64, a, b);
        fb.ret(vec![s]);
        fb.switch_to_block(dead);
        fb.unreachable();
        fb.build();
    }
    let mk_id = {
        // `clean_alloc_ctor`-shaped: the leaf cell is built at register level
        // too — a `U64` lane, which `make_aggregate` and `Const` both spell.
        let mut fb = mb.function("clean_rc_mk_leaf", mk_ty);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let out = fb.make_enum_variant(tree.clone(), 0, vec![x]);
        let cell = fb.heap_alloc(tree.clone(), None, None, AllocOrigin::CleanHeap);
        fb.store(tree.clone(), cell, out);
        let h = fb.cast(CastOp::PtrToPtr, Ty::Ptr, rc.clone(), cell);
        fb.ret(vec![h]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let c40 = fb.uconst(Ty::U64, 40);
        let c2 = fb.uconst(Ty::U64, 2);
        let l1 = fb.call(mk_id, vec![c40]);
        let l2 = fb.call(mk_id, vec![c2]);
        let cell = fb.heap_alloc(tree.clone(), None, None, AllocOrigin::CleanHeap);
        let node = match seed {
            NodeSeed::MakeAggregate => fb.make_enum_variant(tree.clone(), 1, vec![l1, l2]),
            NodeSeed::ConstSeed => {
                let seed = fb.const_value(
                    tree.clone(),
                    Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0), Constant::Int(0)]),
                );
                let n1 = fb.insert_field(tree.clone(), seed, 1, l1);
                fb.insert_field(tree.clone(), n1, 2, l2)
            }
            NodeSeed::ArityOffByOne => fb.make_enum_variant(tree.clone(), 1, vec![l1]),
            NodeSeed::VariantEqualsCount => fb.make_enum_variant(tree.clone(), 2, vec![l1, l2]),
            NodeSeed::VariantMissing => fb.make_aggregate(tree.clone(), vec![l1, l2]),
            NodeSeed::PtrForRcLane => {
                // The raw cell of a second leaf, never cast to `Rc<Tree>`.
                let raw = fb.heap_alloc(tree.clone(), None, None, AllocOrigin::CleanHeap);
                fb.make_enum_variant(tree.clone(), 1, vec![l1, raw])
            }
            NodeSeed::RefForRcLane => {
                let raw = fb.heap_alloc(tree.clone(), None, None, AllocOrigin::CleanHeap);
                let shared = fb.cast(
                    CastOp::PtrToPtr,
                    Ty::Ptr,
                    Ty::Ref(Box::new(tree.clone())),
                    raw,
                );
                fb.make_enum_variant(tree.clone(), 1, vec![l1, shared])
            }
        };
        fb.store(tree.clone(), cell, node);
        let root = fb.cast(CastOp::PtrToPtr, Ty::Ptr, rc.clone(), cell);
        let out = fb.call(sum_id, vec![root]);
        fb.ret(vec![out]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_enum(tree_def());
    m
}

// ---------------------------------------------------------------------------
// POSITIVE — the b6 register seed, now expressible
// ---------------------------------------------------------------------------

#[test]
fn make_aggregate_seeds_a_typed_reference_enum_payload_in_registers() {
    let m = build_rc_tree(NodeSeed::MakeAggregate);
    assert_clean(&m, "make_aggregate enum.0 variant 1 (Rc<Tree>, Rc<Tree>)");
    let codegen = validate_module_for_codegen(&license(&m));
    assert!(
        codegen.is_empty(),
        "the licensed clone must pass the strictest entry point: {codegen:?}"
    );
    assert_eq!(
        run_u64(&m, "program"),
        Some(42),
        "sum over the register-seeded tree: {:?}",
        run_nullary(&m, "program")
    );
}

/// The old seed stays refused EXACTLY as the proof-program row measured it:
/// two `ConstTypeMismatch` (`Rc<enum.0>` expected, `int` found) in
/// `program`, and nothing else — the constant rule is NOT widened. A wider
/// constant rule would be the rejected alternative of the WS3.5 DECIDE (a
/// constant `Rc` / `&mut` has no provenance).
#[test]
fn negative_twin_const_seed_over_typed_reference_lanes_stays_refused() {
    let m = build_rc_tree(NodeSeed::ConstSeed);
    let errors = validate_module(&m);
    let seed_refused = errors
        .iter()
        .filter(|e| {
            matches!(e, ValidationError::ConstTypeMismatch { location, expected, actual }
            if location == "function 'program' bb0" && expected == "Rc<enum.0>" && actual == "int")
        })
        .count();
    assert_eq!(
        seed_refused, 2,
        "the Const seed must stay exactly two ConstTypeMismatch: {errors:?}"
    );
    assert_eq!(
        errors.len(),
        2,
        "no other refusal joins the twin (nothing else about the module changed): {errors:?}"
    );
}

// ---------------------------------------------------------------------------
// MUTATION CONTROLS on the enum construction
// ---------------------------------------------------------------------------

#[test]
fn enum_payload_arity_off_by_one_is_refused() {
    let errors = validate_module(&build_rc_tree(NodeSeed::ArityOffByOne));
    assert!(
        invalid_make_aggregate(
            &errors,
            "1 lane operand(s) supplied, but the type declares 2"
        ),
        "expected InvalidMakeAggregate naming the arity: {errors:?}"
    );
    assert!(
        run_nullary(&build_rc_tree(NodeSeed::ArityOffByOne), "program").is_err(),
        "the interpreter must fail closed on the unvalidated arity"
    );
}

#[test]
fn variant_index_equal_to_variant_count_is_refused() {
    let errors = validate_module(&build_rc_tree(NodeSeed::VariantEqualsCount));
    assert!(
        invalid_make_aggregate(&errors, "variant index 2 is out of range (2 variant(s))"),
        "expected InvalidMakeAggregate naming the range: {errors:?}"
    );
}

#[test]
fn enum_construction_without_a_variant_clause_is_refused() {
    let errors = validate_module(&build_rc_tree(NodeSeed::VariantMissing));
    assert!(
        invalid_make_aggregate(&errors, "an enum construction needs a `variant` index"),
        "expected InvalidMakeAggregate naming the missing variant: {errors:?}"
    );
}

/// EXACTNESS: a lane declared `Rc<Tree>` takes an `Rc<Tree>` operand and
/// nothing else. `Ptr` and `&Tree` are both pointer-like and both wrong —
/// the rule is type equality (`InsertField`'s), never `is_pointer_like`.
#[test]
fn pointer_like_operands_for_an_rc_lane_are_refused_exactly() {
    let errors = validate_module(&build_rc_tree(NodeSeed::PtrForRcLane));
    assert!(
        lane_mismatch(&errors, "lane 1", "Rc<enum.0>", "ptr"),
        "bare Ptr for an Rc<Tree> lane must be OperandTypeMismatch(lane 1): {errors:?}"
    );
    let errors = validate_module(&build_rc_tree(NodeSeed::RefForRcLane));
    assert!(
        lane_mismatch(&errors, "lane 1", "Rc<enum.0>", "&enum.0"),
        "&Tree for an Rc<Tree> lane must be OperandTypeMismatch(lane 1): {errors:?}"
    );
}

// ---------------------------------------------------------------------------
// Struct / tuple / array / record shapes and their mutation controls
// ---------------------------------------------------------------------------

/// `struct Pair { count: u64, tree: Rc<Tree> }` built from `(%n, %t)`, in
/// declaration order or swapped.
fn build_pair(swap_lanes: bool) -> Module {
    let tree = Ty::Enum(EnumId::new(0));
    let rc = Ty::Rc(Box::new(tree.clone()));
    let pair = Ty::Struct(StructId::new(0));
    let mut mb = ModuleBuilder::new("ws3_5_pair");
    let ft = mb.add_func_type(vec![Ty::U64, rc.clone()], vec![Ty::U64]);
    {
        let mut fb = mb.function("mk_pair", ft);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        let n = fb.add_block_param(entry, Ty::U64);
        let t = fb.add_block_param(entry, rc.clone());
        fb.switch_to_block(entry);
        let lanes = if swap_lanes { vec![t, n] } else { vec![n, t] };
        let p = fb.make_aggregate(pair.clone(), lanes);
        let back = fb.extract_field(Ty::U64, p, 0);
        fb.ret(vec![back]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_enum(tree_def());
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "count".into(),
                ty: Ty::U64,
                offset: None,
            },
            FieldDef {
                name: "tree".into(),
                ty: rc,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    m
}

#[test]
fn struct_construction_in_declaration_order_validates() {
    assert_clean(&build_pair(false), "make_aggregate struct.0 (%n, %t)");
}

#[test]
fn struct_lane_order_swapped_is_refused_on_both_lanes() {
    let errors = validate_module(&build_pair(true));
    assert!(
        lane_mismatch(&errors, "lane 0", "u64", "Rc<enum.0>")
            && lane_mismatch(&errors, "lane 1", "Rc<enum.0>", "u64"),
        "swapped (Rc, U64) operands for a (U64, Rc) struct must be refused lane by lane: \
         {errors:?}"
    );
}

/// One function per shape: the instruction under test is the only body
/// instruction besides the return, so a refusal is unambiguously its own.
fn shape_module(name: &str, params: Vec<Ty>, inst: Inst, result_ty: Ty) -> Module {
    let mut module = Module::new(name);
    let ft = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![result_ty],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "probe", ft, BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let mut b = Block::new(BlockId::new(0));
    for (i, ty) in params.into_iter().enumerate() {
        b.params.push((ValueId::new(i as u32), ty));
    }
    let result = ValueId::new(b.params.len() as u32);
    b.body.push(InstrNode::new(inst).with_results(vec![result]));
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

#[test]
fn tuple_and_array_constructions_validate_and_extract() {
    let tuple = Ty::Tuple(vec![Ty::I32, Ty::Bool]);
    let m = shape_module(
        "tuple",
        vec![Ty::I32, Ty::Bool],
        Inst::MakeAggregate {
            ty: tuple.clone(),
            variant: None,
            fields: vec![ValueId::new(0), ValueId::new(1)],
        },
        tuple,
    );
    assert_clean(&m, "make_aggregate tuple(i32, bool)");

    let mut m = Module::new("array");
    let elem = m.add_type(Ty::I32).expect("Module::add_type: test fixture");
    let arr = Ty::Array(elem, 2);
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "probe", ft, BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::I32));
    b.params.push((ValueId::new(1), Ty::I32));
    b.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: arr,
            variant: None,
            fields: vec![ValueId::new(0), ValueId::new(1)],
        })
        .with_results(vec![ValueId::new(2)]),
    );
    b.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_results(vec![ValueId::new(3)]),
    );
    b.body.push(
        InstrNode::new(Inst::ExtractElement {
            ty: Ty::I32,
            array: ValueId::new(2),
            index: ValueId::new(3),
        })
        .with_results(vec![ValueId::new(4)]),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    f.blocks.push(b);
    m.functions.push(f);
    assert_clean(&m, "make_aggregate [i32; 2]");
    let out = Interpreter::with_module(&m)
        .execute_func(
            FuncId::new(0),
            vec![
                InterpretValue::int(Ty::I32, 7).unwrap(),
                InterpretValue::int(Ty::I32, 9).unwrap(),
            ],
        )
        .map(|o| o.returns)
        .expect("array construction executes");
    assert_eq!(
        out[0].as_int().map(|i| i.as_signed()),
        Some(9),
        "element 1 of the built array is operand 1"
    );

    // Array arity: 3 operands for `[i32; 2]`.
    let mut bad = m.clone();
    if let Inst::MakeAggregate { fields, .. } = &mut bad.functions[0].blocks[0].body[0].inst {
        fields.push(ValueId::new(0));
    }
    let errors = validate_module(&bad);
    assert!(
        invalid_make_aggregate(
            &errors,
            "3 lane operand(s) supplied, but the array declares 2"
        ),
        "array arity must be refused by name: {errors:?}"
    );
}

#[test]
fn a_variant_clause_on_a_struct_is_refused() {
    let tuple = Ty::Tuple(vec![Ty::I32]);
    let m = shape_module(
        "variant_on_tuple",
        vec![Ty::I32],
        Inst::MakeAggregate {
            ty: tuple.clone(),
            variant: Some(0),
            fields: vec![ValueId::new(0)],
        },
        tuple,
    );
    let errors = validate_module(&m);
    assert!(
        invalid_make_aggregate(&errors, "a `variant` index is only meaningful for an enum"),
        "{errors:?}"
    );
}

/// Vectors keep `InsertElement`, fat pointers keep `PtrFromParts`, and a
/// scalar is not an aggregate at all: each is `InvalidMakeAggregate`, never a
/// silently accepted value of the declared type.
#[test]
fn non_aggregate_types_are_refused_by_name() {
    for (label, ty, params) in [
        ("scalar", Ty::I32, vec![Ty::I32]),
        (
            "vector",
            Ty::Vector(Box::new(Ty::I32), 4),
            vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32],
        ),
        (
            "fat pointer",
            Ty::FatPtr(trust_ir::ty::FatPtrKind::Str),
            vec![Ty::Ptr, Ty::U64],
        ),
    ] {
        let fields = (0..params.len() as u32).map(ValueId::new).collect();
        let m = shape_module(
            label,
            params,
            Inst::MakeAggregate {
                ty: ty.clone(),
                variant: None,
                fields,
            },
            ty,
        );
        let errors = validate_module(&m);
        assert!(
            invalid_make_aggregate(&errors, "not a type make_aggregate builds"),
            "{label}: expected InvalidMakeAggregate: {errors:?}"
        );
    }
}

/// WS3.14 composition: the variant `B(!)`-shaped (`Never` field) has no value,
/// so building it is `UninhabitedVariantConstructed` — the same refusal
/// `Const` gets — and never a lane check on a lane that cannot exist.
#[test]
fn an_uninhabited_variant_cannot_be_constructed() {
    let e = Ty::Enum(EnumId::new(0));
    let mut m = shape_module(
        "uninhabited",
        vec![Ty::I32],
        Inst::MakeAggregate {
            ty: e.clone(),
            variant: Some(1),
            fields: vec![ValueId::new(0)],
        },
        e,
    );
    let never = m
        .add_type(Ty::Never)
        .expect("Module::add_type: test fixture");
    let _ = never;
    m.add_enum(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::I32],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![Ty::Never],
                field_names: vec![],
            },
        ],
    ));
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UninhabitedVariantConstructed { enum_name, variant: 1, variant_name, .. }
            if enum_name == "E" && variant_name == "B"
        )),
        "expected UninhabitedVariantConstructed for variant B: {errors:?}"
    );
    // Control: variant A of the same enum builds.
    if let Inst::MakeAggregate { variant, .. } = &mut m.functions[0].blocks[0].body[0].inst {
        *variant = Some(0);
    }
    assert_clean(&m, "the inhabited variant of the same enum");
}

// ---------------------------------------------------------------------------
// The refinement consumption rule — the SAME one `InsertField` uses
// ---------------------------------------------------------------------------

/// `struct Row { key: refine<i64, P> }`, built by `make_aggregate` from a
/// parameter of type `carrier` (or by `insert_field`, for the reference
/// verdict).
fn refined_row(carrier: Ty, lane: Ty, spell_insert: bool) -> Module {
    let mut module = Module::new(if spell_insert {
        "refined_insert"
    } else {
        "refined_make"
    });
    let row = StructId::new(0);
    module.add_struct(StructDef {
        id: row,
        name: "Row".into(),
        fields: vec![FieldDef {
            name: "key".into(),
            ty: lane,
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Struct(row), carrier.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "write", ft, BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::Struct(row)));
    b.params.push((ValueId::new(1), carrier));
    let inst = if spell_insert {
        Inst::InsertField {
            ty: Ty::Struct(row),
            aggregate: ValueId::new(0),
            field: 0,
            value: ValueId::new(1),
        }
    } else {
        Inst::MakeAggregate {
            ty: Ty::Struct(row),
            variant: None,
            fields: vec![ValueId::new(1)],
        }
    };
    b.body
        .push(InstrNode::new(inst).with_results(vec![ValueId::new(2)]));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

fn with_preds(mut module: Module) -> (Module, trust_ir::value::TyId, trust_ir::value::PredId) {
    let i64_ty = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    let u = module
        .intern_universe(Universe::IntRange { lo: 1, hi: 8 })
        .expect("Module::intern_universe: test fixture")
        .expect("canonical");
    let member = module
        .intern_pred(Pred::InUniverse(u, Space::Member))
        .expect("Module::intern_pred: test fixture")
        .expect("in range");
    (module, i64_ty, member)
}

#[test]
fn an_unrefined_operand_for_a_refined_lane_is_refused_exactly_like_insert_field() {
    // Both spellings are built on the same table so the refined lane type is
    // literally the same `Ty`.
    let (base, i64_ty, member) = with_preds(Module::new("seed"));
    let refined = Ty::Refine(i64_ty, member);
    let build = |spell_insert: bool| {
        let mut m = refined_row(Ty::I64, refined.clone(), spell_insert);
        m.types = base.types.clone();
        m.universes = base.universes.clone();
        m.predicates = base.predicates.clone();
        m
    };
    let kinds = |m: &Module| -> Vec<String> {
        let mut names: Vec<String> = validate_module(m)
            .iter()
            .map(|e| {
                format!("{e:?}")
                    .split(['(', '{', ' '])
                    .next()
                    .unwrap_or("")
                    .to_string()
            })
            .collect();
        names.sort();
        names
    };
    let insert = kinds(&build(true));
    let make = kinds(&build(false));
    assert!(
        make.iter().any(|k| k == "RefinementNotImplied"),
        "an unrefined i64 for a refined lane must be RefinementNotImplied: {make:?}"
    );
    assert_eq!(
        make, insert,
        "make_aggregate must refuse with the SAME error kinds insert_field does"
    );

    // Control: the operand carries the lane's own refinement — both spellings clean.
    let ok = |spell_insert: bool| {
        let mut m = refined_row(refined.clone(), refined.clone(), spell_insert);
        m.types = base.types.clone();
        m.universes = base.universes.clone();
        m.predicates = base.predicates.clone();
        m
    };
    assert_clean(
        &ok(false),
        "refined operand -> refined lane (make_aggregate)",
    );
    assert_clean(&ok(true), "refined operand -> refined lane (insert_field)");
}

// ---------------------------------------------------------------------------
// REVIEW — adversarial inputs the increment did not write
// ---------------------------------------------------------------------------

/// A legitimate module must never CRASH a validator. Before the review every
/// digest-keyed entry point — the linked import walk (root or resolved
/// candidate) and the bundle binding — panicked inside `stable_digest` on a
/// module carrying `make_aggregate` (the canonical writer had no tag for it);
/// the review made each refuse by name (`ModuleHasNoWireIdentity`). Since the
/// INST wire batch (v51, Inst tag 60) the module HAS a wire identity, so each
/// entry point now HASHES it: the linked root validates, a bundle binds by
/// digest (and a bundle for another module is `NativeBundleNotForThisModule`,
/// a computed digest, not a refusal), and a resolved candidate is
/// authenticated against its digest like any other.
#[test]
// The bundle path is exercised through the deprecated legacy coverage rule,
// which keeps its wire-identity probe until it is deleted.
#[allow(deprecated)]
fn a_make_aggregate_module_has_a_wire_identity_on_every_digest_keyed_path() {
    use trust_ir::proof::{ProofLineageManifest, RejectingModuleProofAuthority};
    use trust_ir::request::{NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle};
    use trust_ir_build::{ModuleSet, coverage_assurance_report, validate_linked_module};

    let m = build_rc_tree(NodeSeed::MakeAggregate);
    assert_clean(&m, "the structural validator admits the module");
    assert_eq!(trust_ir_build::wire_identity_blocker(&m), None);
    let digest = m.stable_digest();
    assert_eq!(m.stable_digest(), digest);
    #[cfg(feature = "binary")]
    {
        let bytes = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
        let (decoded, version) =
            trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decodes");
        assert_eq!(
            version.get(),
            trust_ir::binary::INST_WIRE_BATCH_FORMAT_VERSION
        );
        assert_eq!(decoded, m);
        assert_eq!(decoded.stable_digest(), digest);
    }

    // Root of a linked walk (no imports at all): hashed and validated.
    let none = ModuleSet::new(std::iter::empty::<&Module>());
    let linked = validate_linked_module(&m, &none, &RejectingModuleProofAuthority);
    assert!(linked.is_ok(), "{:?}", linked.errors());

    // Bundle binding: a bundle for THIS module binds; one for ANOTHER module
    // is refused as a digest mismatch — the digest was computed.
    let bundle_for = |module: &Module| {
        NativeVerificationBundle::new(
            NativeBundleProducer::TrustIr,
            NativeAdapterInput::TrustIrModule,
            module.stable_digest(),
            module.clone(),
            ProofLineageManifest::default(),
        )
    };
    let own = coverage_assurance_report(&m, Some(&bundle_for(&m)));
    assert!(own.is_checked(), "{:?}", own.into_errors());
    let other = Module::new("ws3_5_some_other_module");
    let report = coverage_assurance_report(&m, Some(&bundle_for(&other)));
    assert!(!report.is_checked());
    let errors = report.into_errors();
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::NativeBundleNotForThisModule { expected, .. }] if *expected == digest
        ),
        "{errors:?}"
    );

    // Resolved CANDIDATE of an import row: authenticated against its digest.
    // A row recording some OTHER digest is refused for the mismatch, never
    // for a missing wire identity.
    let mut importer = Module::new("importer");
    importer.imports.push(trust_ir::ModuleImport {
        name: "ws3_5_rc_tree".into(),
        digest: trust_ir::proof::ProofDigest::sha256([7u8; 32]),
        producer: Some(Producer::Clean),
        scheme: trust_ir::IdentityScheme::CURRENT,
    });
    let resolver = |_import: &trust_ir::ModuleImport| Some(&m);
    let linked = validate_linked_module(&importer, &resolver, &RejectingModuleProofAuthority);
    assert!(
        linked.errors().iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { import: 0, detail, .. }
                if !detail.contains("no wire identity")
        )),
        "{:?}",
        linked.errors()
    );
    assert!(
        !linked
            .errors()
            .iter()
            .any(|e| matches!(e, ValidationError::ModuleHasNoWireIdentity { .. })),
        "{:?}",
        linked.errors()
    );
}

/// The implementer's claim that a lane REACHING a nominal dialect type is
/// refused by the transport whitelist, measured: `struct { d: dialect }` built
/// from a dialect-typed block parameter is `InvalidDialectType`, never a
/// silently accepted value.
#[test]
fn a_dialect_lane_is_refused_by_the_nominal_transport_whitelist() {
    let dialect = Ty::Dialect(Box::new(trust_ir::ty::DialectTy::new(
        "example", "opaque", 1,
    )));
    let s = Ty::Struct(StructId::new(0));
    let mut m = shape_module(
        "dialect_lane",
        vec![dialect.clone()],
        Inst::MakeAggregate {
            ty: s.clone(),
            variant: None,
            fields: vec![ValueId::new(0)],
        },
        s,
    );
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Wrap".into(),
        fields: vec![FieldDef {
            name: "d".into(),
            ty: dialect,
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    let errors = validate_module(&m);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidDialectType { .. })),
        "a dialect lane must be InvalidDialectType: {errors:?}"
    );
    assert!(
        !invalid_make_aggregate(&errors, "not a type make_aggregate builds"),
        "the struct itself is a type the instruction builds; only its LANE is refused: {errors:?}"
    );
}

/// An enum WITHOUT a layout descriptor is the common producer case (the
/// canonical tagged-union layout applies). Construction must validate and
/// the interpreter must build the `[tag, fields..]` value under that layout:
/// `variant 0 (%x, %b)` of `enum E { A(i32, bool), B }` then lane 1 reads
/// back operand 0 and lane 0 is the discriminant.
#[test]
fn an_enum_without_a_layout_descriptor_constructs_under_the_canonical_layout() {
    let e = Ty::Enum(EnumId::new(0));
    let mut m = Module::new("canonical_enum");
    m.add_enum(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::I32, Ty::Bool],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    ));
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::Bool],
            returns: vec![Ty::I32, Ty::U8],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "probe", ft, BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::I32));
    b.params.push((ValueId::new(1), Ty::Bool));
    b.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: e.clone(),
            variant: Some(0),
            fields: vec![ValueId::new(0), ValueId::new(1)],
        })
        .with_results(vec![ValueId::new(2)]),
    );
    b.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: Ty::I32,
            aggregate: ValueId::new(2),
            field: 1,
        })
        .with_results(vec![ValueId::new(3)]),
    );
    b.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U8,
            aggregate: ValueId::new(2),
            field: 0,
        })
        .with_results(vec![ValueId::new(4)]),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3), ValueId::new(4)],
    }));
    f.blocks.push(b);
    m.functions.push(f);
    assert_clean(
        &m,
        "make_aggregate enum.0 variant 0 (%x, %b) without a descriptor",
    );
    let out = Interpreter::with_module(&m)
        .execute_func(
            FuncId::new(0),
            vec![
                InterpretValue::int(Ty::I32, -5).unwrap(),
                InterpretValue::bool(true),
            ],
        )
        .map(|o| o.returns)
        .expect("canonical-layout enum construction executes");
    assert_eq!(out[0].as_int().map(|i| i.as_signed()), Some(-5));
    assert_eq!(
        out[1].as_int().map(|i| i.as_unsigned()),
        Some(0),
        "the tag lane is discriminants[0]"
    );

    // Mutation: `variant 1` (the fieldless `B`) with A's two lanes — arity.
    if let Inst::MakeAggregate { variant, .. } = &mut m.functions[0].blocks[0].body[0].inst {
        *variant = Some(1);
    }
    let errors = validate_module(&m);
    assert!(
        invalid_make_aggregate(
            &errors,
            "2 lane operand(s) supplied, but the type declares 0 lane(s)"
        ),
        "{errors:?}"
    );
}

/// Information flow: a `Tainted` lane taints the built aggregate, so a
/// `TrustedSink` consuming the aggregate is refused — the new spelling is
/// not a laundering path for a tainted value (the operand visitor covers
/// every lane).
#[test]
fn a_tainted_lane_taints_the_aggregate_it_is_built_into() {
    use trust_ir::proof::ProofAnnotation;
    let tuple = Ty::Tuple(vec![Ty::I32, Ty::I32]);
    let mut m = Module::new("taint");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![tuple.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "probe", ft, BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::I32));
    b.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: ValueId::new(0),
        })
        .with_results(vec![ValueId::new(1)])
        .with_proof(ProofAnnotation::Tainted),
    );
    b.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: tuple,
            variant: None,
            fields: vec![ValueId::new(0), ValueId::new(1)],
        })
        .with_results(vec![ValueId::new(2)]),
    );
    b.body.push(
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        })
        .with_proof(ProofAnnotation::TrustedSink),
    );
    f.blocks.push(b);
    m.functions.push(f);
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::TaintedValueReachesTrustedSink { value: 2, .. }
        )),
        "the aggregate built from a tainted lane must reach the sink as tainted: {errors:?}"
    );
    // Control: drop the taint and the sink is clean.
    m.functions[0].blocks[0].body[0].proofs.clear();
    assert_clean(&m, "untainted lanes -> trusted sink");
}

/// A `Refine` as the AGGREGATE type (not a lane) is not a type the
/// instruction builds — it must be `InvalidMakeAggregate`, never a value
/// admitted at the refined type without its predicate being established.
#[test]
fn a_refined_aggregate_type_is_refused_as_not_buildable() {
    let tuple = Ty::Tuple(vec![Ty::I32]);
    let base_m = shape_module(
        "refined_ty",
        vec![Ty::I32],
        Inst::MakeAggregate {
            ty: tuple.clone(),
            variant: None,
            fields: vec![ValueId::new(0)],
        },
        tuple.clone(),
    );
    let mut m = base_m;
    let base = m.add_type(tuple).expect("Module::add_type: test fixture");
    let u = m
        .intern_universe(Universe::IntRange { lo: 1, hi: 8 })
        .expect("Module::intern_universe: test fixture")
        .expect("canonical");
    let pred = m
        .intern_pred(Pred::InUniverse(u, Space::Member))
        .expect("Module::intern_pred: test fixture")
        .expect("in range");
    let refined = Ty::Refine(base, pred);
    m.functions[0].blocks[0].body[0].inst = Inst::MakeAggregate {
        ty: refined.clone(),
        variant: None,
        fields: vec![ValueId::new(0)],
    };
    m.func_types[0].returns = vec![refined];
    let errors = validate_module(&m);
    assert!(
        invalid_make_aggregate(&errors, "not a type make_aggregate builds"),
        "{errors:?}"
    );
}
