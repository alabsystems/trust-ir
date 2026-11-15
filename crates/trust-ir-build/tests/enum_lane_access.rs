// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// audit c06 — `ExtractField` / `InsertField` on an ENUM value, static half.
// ══════════════════════════════════════════════════════════════════════════
//
// Before this rule `validate_field_access` returned early on `Ty::Enum(_)`
// ("left to dedicated enum lowering" — which did not exist) and skipped EVERY
// check: the lane index, the declared `ExtractField` type, the inserted
// VALUE's type and even `InsertField`'s RESULT type, so `insert_field i64
// <enum>` validated and recorded an `i64` for an enum value. The refinement
// consumption rule (`aggregate_field_tys`) had no enum arm either.
//
// The value model is `[tag, fields..]` (the reference interpreter's
// `Aggregate([tag, fields...])`, CLAUDE.md v37): lane 0 is the discriminant at
// `EnumDef::canonical_tag_repr().ty()`, and lane `i >= 1` is field `i - 1` of
// whichever variant is ACTIVE. Roadmap increment WS2.2 (F-029, static half)
// names each refusal with the error the rest of the aggregate family uses:
//
//   * no canonical tag repr: EVERY projection, `FieldAccessInvalid`;
//   * a lane index beyond every variant's arity: `FieldAccessInvalid`
//     "field {i} is out of range for every variant of {ty}";
//   * a tag-lane READ at a type other than the canonical tag repr:
//     `OperandTypeMismatch { role: "field" }`;
//   * ANY tag-lane WRITE (`insert_field` lane 0): `FieldAccessInvalid`
//     "insert_field cannot rewrite an enum discriminant; construct the variant
//     with Const" — a re-tag keeps the old variant's payload under the new tag;
//   * a payload-lane read/write at a type that is the lane type of NO variant:
//     `OperandTypeMismatch { role: "field" | "value", expected: "one of {..}" }`;
//   * an `InsertField` whose declared result is not the aggregate's own type:
//     `OperandTypeMismatch { role: "result" }`, checked first, for every
//     aggregate kind;
//
// plus the consumption rule over the SET of variant lane types.
//
// What stays DYNAMIC (the variant-active half): a lane that is right for SOME
// variant, read or written on a value whose active variant is another one.
// That is undefined behaviour (`docs/ub-numerics-policy.md` §4); the reference
// interpreter refuses it at run time with `UndefinedBehavior "enum {ty}: lane
// {i} belongs to no field of active variant {name}"`. `mutation_control_*`
// pins that split. HONEST LIMIT: a wrong-variant lane with the SAME type in
// both variants is invisible to both engines until the variant-indexed
// projection (WS2.2 DECIDE (a), a reserved wire version) lands —
// `honest_limit_*` pins that too, so its closing is a visible flip.
//
// The ported GAP ratchet is `b6.enum.payload_projection_unchecked` from the
// 2026-09-17 two-language proof program (partb/tests/b6_data_carriers.rs):
// there it asserted the hole was PRESENT; here it asserts it is CLOSED.

use trust_ir::constant::Constant;
use trust_ir::inst::{Inst, SwitchCase};
use trust_ir::interpret::{InterpretOptions, InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumVariant, Ty};
use trust_ir::value::{BlockId, EnumId, FuncId, PredId, TyId, ValueId};
use trust_ir::{Block, BodyGate, FuncTy, Function, Module, Pred, Producer, Space, Universe};
use trust_ir_build::{
    ModuleBuilder, ValidationError, validate_module, validate_module_for_codegen,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn render(errors: &[ValidationError]) -> String {
    errors
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join(" | ")
}

fn assert_clean(module: &Module, what: &str) {
    let errors = validate_module(module);
    assert!(
        errors.is_empty(),
        "{what} must validate clean, got {} error(s): {}",
        errors.len(),
        render(&errors)
    );
}

/// The one named refusal a twin expects.
enum Want<'a> {
    /// `FieldAccessInvalid` whose reason contains the fragment.
    Invalid(&'a str),
    /// `OperandTypeMismatch` on `role`, whose `expected` contains the fragment
    /// and whose `actual` is exactly the given type.
    Mismatch {
        role: &'a str,
        expected: &'a str,
        actual: String,
    },
}

/// Exactly one error, and it is `want` at `want_op`.
fn assert_one_refusal(errors: &[ValidationError], what: &str, want_op: &str, want: Want<'_>) {
    assert_eq!(
        errors.len(),
        1,
        "{what}: expected exactly one error, got {}: {}",
        errors.len(),
        render(errors)
    );
    match (&errors[0], want) {
        (ValidationError::FieldAccessInvalid { op, reason, .. }, Want::Invalid(fragment)) => {
            assert_eq!(op, want_op, "{what}: op");
            assert!(
                reason.contains(fragment),
                "{what}: expected {fragment:?} in the reason, got {reason:?}"
            );
        }
        (
            ValidationError::OperandTypeMismatch {
                op,
                role,
                expected,
                actual,
                ..
            },
            Want::Mismatch {
                role: want_role,
                expected: want_expected,
                actual: want_actual,
            },
        ) => {
            assert_eq!(op, want_op, "{what}: op");
            assert_eq!(role, want_role, "{what}: role");
            assert!(
                expected.contains(want_expected),
                "{what}: expected {want_expected:?} in `expected`, got {expected:?}"
            );
            assert_eq!(*actual, want_actual, "{what}: actual");
        }
        (got, _) => panic!("{what}: wrong refusal kind: {got:?}"),
    }
}

fn mismatch<'a>(role: &'a str, expected: &'a str, actual: &Ty) -> Want<'a> {
    Want::Mismatch {
        role,
        expected,
        actual: actual.to_string(),
    }
}

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
        .map_err(|e| format!("{:?}: {e}", e.code))
}

fn run_u64(module: &Module, entry: &str) -> Option<u128> {
    run_nullary(module, entry)
        .ok()?
        .first()?
        .as_int()
        .map(|i| i.as_unsigned())
}

fn replace_inst(
    m: &mut Module,
    func: &str,
    pred: impl Fn(&Inst) -> bool,
    new: impl Fn(&Inst) -> Inst,
) -> usize {
    let mut n = 0;
    let f = m
        .functions
        .iter_mut()
        .find(|f| f.name == func)
        .expect("function");
    for b in &mut f.blocks {
        for node in &mut b.body {
            if pred(&node.inst) {
                node.inst = new(&node.inst);
                n += 1;
            }
        }
    }
    n
}

// ---------------------------------------------------------------------------
// The Tree fixture (ported from b6_data_carriers.rs): Rust builds a tree, a
// Clean function walks it by projecting enum lanes.
//
//   enum Tree { leaf(u64), node(ptr, ptr) }   -- canonical tag repr: u8
//   lanes: 0 = tag (u8); 1 = leaf.0 (u64) | node.0 (ptr); 2 = node.1 (ptr)
// ---------------------------------------------------------------------------

fn tree_def(layout: Option<EnumLayoutDescriptor>) -> EnumDef {
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
                fields: vec![Ty::Ptr, Ty::Ptr],
                field_names: vec!["left".into(), "right".into()],
            },
        ],
    );
    def.layout = layout;
    def
}

/// Payload first, tag LAST — the rustc-style reordering a producer reads off
/// `Variants::Multiple`, not trust-ir's canonical image.
fn tree_direct_layout() -> EnumLayoutDescriptor {
    EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 16 },
        size: 24,
        align: 8,
        variant_field_offsets: vec![vec![0], vec![0, 8]],
    }
}

fn build_tree(layout: Option<EnumLayoutDescriptor>) -> Module {
    let tree = Ty::Enum(EnumId::new(0));
    let mut mb = ModuleBuilder::new("c06_tree");
    let sum_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let mk_ty = mb.add_func_type(vec![Ty::U64], vec![tree.clone()]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);

    let sum_id = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    {
        let mut fb = mb.function("clean_tree_sum", sum_ty);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("Tree.sum");
        // An authority the codegen layer binds to NO evidence: since WS1.5,
        // `clean-kernel-tv` demands a kernel-rechecked TranslationValidation
        // certificate per body, which this lane fixture does not mint.
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-direct-lane-structural".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let leaf = fb.create_block();
        let node = fb.create_block();
        let dead = fb.create_block();
        let t = fb.add_block_param(entry, Ty::Ptr);
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
        let l = fb.extract_field(Ty::Ptr, v, 1);
        let r = fb.extract_field(Ty::Ptr, v, 2);
        let a = fb.call(sum_id, vec![l]);
        let b = fb.call(sum_id, vec![r]);
        let s = fb.add(Ty::U64, a, b);
        fb.ret(vec![s]);
        fb.switch_to_block(dead);
        fb.unreachable();
        fb.build();
    }
    let mk_id = {
        let mut fb = mb.function("clean_mk_leaf", mk_ty);
        fb.set_producer(Producer::Clean);
        // An authority the codegen layer binds to NO evidence: since WS1.5,
        // `clean-kernel-tv` demands a kernel-rechecked TranslationValidation
        // certificate per body, which this lane fixture does not mint.
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-direct-lane-structural".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let seed = fb.const_value(
            tree.clone(),
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
        );
        let out = fb.insert_field(tree.clone(), seed, 1, x);
        fb.ret(vec![out]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let p1 = fb.alloca(tree.clone());
        let p2 = fb.alloca(tree.clone());
        let root = fb.alloca(tree.clone());
        let c40 = fb.uconst(Ty::U64, 40);
        let c2 = fb.uconst(Ty::U64, 2);
        let l1 = fb.call(mk_id, vec![c40]);
        let l2 = fb.call(mk_id, vec![c2]);
        fb.store(tree.clone(), p1, l1);
        fb.store(tree.clone(), p2, l2);
        let seed = fb.const_value(
            tree.clone(),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0), Constant::Int(0)]),
        );
        let n1 = fb.insert_field(tree.clone(), seed, 1, p1);
        let n2 = fb.insert_field(tree.clone(), n1, 2, p2);
        fb.store(tree.clone(), root, n2);
        let out = fb.call(sum_id, vec![root]);
        fb.ret(vec![out]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_enum(tree_def(layout));
    m
}

// ---------------------------------------------------------------------------
// (a) POSITIVE — the well-formed module still validates and runs
// ---------------------------------------------------------------------------

#[test]
fn the_tree_module_validates_for_codegen_and_runs() {
    for (what, layout) in [
        ("direct descriptor", Some(tree_direct_layout())),
        ("canonical layout", None),
    ] {
        let m = build_tree(layout);
        assert_clean(&m, what);
        let codegen = validate_module_for_codegen(&m);
        assert!(
            codegen.is_empty(),
            "{what}: validate_module_for_codegen must accept every well-typed lane access, got {}",
            render(&codegen)
        );
        assert_eq!(run_u64(&m, "program"), Some(42), "{what}: 40 + 2");
    }
}

// ---------------------------------------------------------------------------
// (d) THE PORTED RATCHET — b6.enum.payload_projection_unchecked, now CLOSED
// ---------------------------------------------------------------------------

/// ONE change to the well-formed Tree module: the `leaf` arm projects lane 2
/// (which only `node` has, and at `ptr`) as `u64`. At trust-ir 4efb21bc this
/// validated — also for codegen — and only the interpreter refused it. Now the
/// validator refuses it statically, naming the lane and the variant types.
#[test]
fn b6_enum_payload_projection_unchecked_is_closed() {
    let m = build_tree(Some(tree_direct_layout()));
    let mut wrong = m.clone();
    let n = replace_inst(
        &mut wrong,
        "clean_tree_sum",
        |i| {
            matches!(
                i,
                Inst::ExtractField {
                    ty: Ty::U64,
                    field: 1,
                    ..
                }
            )
        },
        |i| match i {
            Inst::ExtractField { ty, aggregate, .. } => Inst::ExtractField {
                ty: ty.clone(),
                aggregate: *aggregate,
                field: 2,
            },
            _ => unreachable!(),
        },
    );
    assert_eq!(n, 1);

    let errors = validate_module_for_codegen(&wrong);
    assert_one_refusal(
        &errors,
        "b6.enum.payload_projection_unchecked (codegen)",
        "extract_field",
        mismatch("field", "one of {node: ptr}", &Ty::U64),
    );
    assert_one_refusal(
        &validate_module(&wrong),
        "b6.enum.payload_projection_unchecked (validate_module)",
        "extract_field",
        mismatch("field", "one of {node: ptr}", &Ty::U64),
    );
    // The Display text says what and why.
    let text = errors[0].to_string();
    assert!(
        text.contains("extract_field field type mismatch: expected one of {node: ptr}, got u64"),
        "{text}"
    );
}

// ---------------------------------------------------------------------------
// (b) NEGATIVE TWINS — one probe instruction over the Tree enum
// ---------------------------------------------------------------------------

/// ```text
/// fn probe(t: Tree, x: <value_ty>) { %r = <inst over t, x>; ret }
/// ```
/// One instruction and nothing downstream of it, so each twin fires EXACTLY
/// the error its axis carries.
fn probe(value_ty: Ty, inst: Inst) -> Module {
    let tree = Ty::Enum(EnumId::new(0));
    let mut m = Module::new("c06_probe");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![tree.clone(), value_ty.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "probe", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), tree));
    b.params.push((ValueId::new(1), value_ty));
    b.body
        .push(InstrNode::new(inst).with_results(vec![ValueId::new(2)]));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    m.functions.push(f);
    m.add_enum(tree_def(None));
    m
}

fn extract(ty: Ty, field: u32) -> Module {
    probe(
        Ty::U64,
        Inst::ExtractField {
            ty,
            aggregate: ValueId::new(0),
            field,
        },
    )
}

fn insert(result_ty: Ty, field: u32, value_ty: Ty) -> Module {
    probe(
        value_ty,
        Inst::InsertField {
            ty: result_ty,
            aggregate: ValueId::new(0),
            field,
            value: ValueId::new(1),
        },
    )
}

fn tree() -> Ty {
    Ty::Enum(EnumId::new(0))
}

/// Every lane at every type SOME variant gives it, both directions: the
/// accept side of every twin below. (The tag lane is readable only — see
/// `a_tag_lane_write_is_refused_at_every_type`.)
#[test]
fn every_lane_some_variant_carries_validates() {
    for (field, ty) in [(0, Ty::U8), (1, Ty::U64), (1, Ty::Ptr), (2, Ty::Ptr)] {
        assert_clean(
            &extract(ty.clone(), field),
            &format!("extract_field {ty} lane {field}"),
        );
        if field == 0 {
            continue;
        }
        assert_clean(
            &insert(tree(), field, ty.clone()),
            &format!("insert_field lane {field} value {ty}"),
        );
    }
}

#[test]
fn a_lane_beyond_every_variants_arity_is_refused() {
    // Twin of `extract_field ptr t, 2` (node's last lane): one past it.
    assert_one_refusal(
        &validate_module(&extract(Ty::Ptr, 3)),
        "extract lane 3",
        "extract_field",
        Want::Invalid(
            "field 3 is out of range for every variant of enum.0 (the widest variant has 2 \
             field(s)",
        ),
    );
    assert_one_refusal(
        &validate_module(&insert(tree(), 3, Ty::Ptr)),
        "insert lane 3",
        "insert_field",
        Want::Invalid("field 3 is out of range for every variant of enum.0"),
    );
    // The notes' wildly-out-of-range index.
    assert_one_refusal(
        &validate_module(&extract(Ty::U64, 99)),
        "extract lane 99",
        "extract_field",
        Want::Invalid("field 99 is out of range for every variant of enum.0"),
    );
}

#[test]
fn a_declared_type_that_matches_no_variant_is_refused() {
    // Lane 1 is `u64` (leaf) or `ptr` (node) — never `i64` / `f64`.
    for ty in [Ty::I64, Ty::F64, Ty::U8] {
        assert_one_refusal(
            &validate_module(&extract(ty.clone(), 1)),
            &format!("extract lane 1 as {ty}"),
            "extract_field",
            mismatch("field", "one of {leaf: u64, node: ptr}", &ty),
        );
        assert_one_refusal(
            &validate_module(&insert(tree(), 1, ty.clone())),
            &format!("insert lane 1 value {ty}"),
            "insert_field",
            mismatch("value", "one of {leaf: u64, node: ptr}", &ty),
        );
    }
    // Lane 2 exists only on `node`, at `ptr`: `u64` is leaf's LANE 1 type,
    // not anything's lane 2.
    assert_one_refusal(
        &validate_module(&insert(tree(), 2, Ty::U64)),
        "insert lane 2 value u64",
        "insert_field",
        mismatch("value", "one of {node: ptr}", &Ty::U64),
    );
}

#[test]
fn a_tag_lane_at_a_non_canonical_type_is_refused() {
    // Tree's discriminants {0, 1} with no repr hint: canonical tag = u8.
    assert_eq!(
        tree_def(None).canonical_tag_repr().map(|r| r.ty()),
        Some(Ty::U8)
    );
    for ty in [Ty::U64, Ty::I8, Ty::U32] {
        assert_one_refusal(
            &validate_module(&extract(ty.clone(), 0)),
            &format!("extract tag as {ty}"),
            "extract_field",
            mismatch("field", "u8", &ty),
        );
        assert_one_refusal(
            &validate_module(&insert(tree(), 0, ty.clone())),
            &format!("insert tag value {ty}"),
            "insert_field",
            Want::Invalid(
                "insert_field cannot rewrite an enum discriminant; construct the variant with \
                 Const",
            ),
        );
    }
    // A repr hint moves the tag type, and the rule follows it exactly.
    let mut hinted = extract(Ty::U32, 0);
    hinted.enums[0].repr = Some(trust_ir::ty::EnumTagRepr::U32);
    assert_clean(&hinted, "extract tag as u32 under repr(u32)");
    let mut hinted_wrong = extract(Ty::U8, 0);
    hinted_wrong.enums[0].repr = Some(trust_ir::ty::EnumTagRepr::U32);
    assert_one_refusal(
        &validate_module(&hinted_wrong),
        "extract tag as u8 under repr(u32)",
        "extract_field",
        mismatch("field", "u32", &Ty::U8),
    );
}

/// `insert_field i64 <enum>` — the notes' result-type confusion. It used to
/// validate and record `i64` for an enum value.
#[test]
fn an_insert_field_result_typed_other_than_the_enum_is_refused() {
    for result in [Ty::I64, Ty::U64, Ty::Ptr] {
        let errors = validate_module(&insert(result.clone(), 1, Ty::U64));
        assert_eq!(errors.len(), 1, "result {result}: {}", render(&errors));
        assert!(
            matches!(
                &errors[0],
                ValidationError::OperandTypeMismatch { op, role, expected, actual, .. }
                    if op == "insert_field" && role == "result"
                        && expected == "enum.0" && *actual == result.to_string()
            ),
            "result {result}: expected OperandTypeMismatch on the result role, got {}",
            render(&errors)
        );
    }
}

// ---------------------------------------------------------------------------
// (c) MUTATION CONTROL — the dynamic residue (audit c06, variant-active half)
// ---------------------------------------------------------------------------

/// A lane that IS right for some variant, used on a value whose active variant
/// is another one. ONE change to the well-formed Tree module: the `node`
/// seed in `program` is re-tagged as a `leaf` (`[0, 0]`), so the following
/// `insert_field tree n, 1, <ptr>` writes node's lane-1 type into a leaf.
///
/// This is NOT statically decidable from the type — lane 1 at `ptr` is
/// exactly what `node` carries — so the validator must still accept it (a rule
/// that refused it would also refuse the well-formed `node` arm). It is
/// undefined behaviour (`docs/ub-numerics-policy.md` §4), and the variant-aware
/// interpreter (WS2.2 item 5) is what refuses it, naming the active variant.
#[test]
fn mutation_control_a_different_variants_lane_still_validates() {
    let m = build_tree(Some(tree_direct_layout()));
    let mut retagged = m.clone();
    let n = replace_inst(
        &mut retagged,
        "program",
        |i| matches!(i, Inst::Const { value: Constant::Aggregate(e), .. } if e.len() == 3),
        |i| match i {
            Inst::Const { ty, .. } => Inst::Const {
                ty: ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
            },
            _ => unreachable!(),
        },
    );
    assert_eq!(n, 1);
    assert!(
        validate_module_for_codegen(&retagged).is_empty(),
        "the variant-active half is dynamic and must still validate: {}",
        render(&validate_module_for_codegen(&retagged))
    );
    let run = run_nullary(&retagged, "program");
    assert!(
        matches!(&run, Err(e) if e.starts_with("UndefinedBehavior")
            && e.contains("enum enum.0: lane 1 belongs to no field of active variant leaf")
            && e.contains("lane 1 of leaf is u64; the access is at ptr")),
        "the interpreter refuses the wrong-variant write (node's ptr into leaf's u64 lane) \
         at run time: {run:?}"
    );

    // And the static probe form of the same residue: reading node's lane 2 off
    // an arbitrary Tree value validates (the probe cannot know the variant).
    assert_clean(&extract(Ty::Ptr, 2), "extract node lane 2 from any Tree");
}

// ---------------------------------------------------------------------------
// The consumption rule at an enum lane
// ---------------------------------------------------------------------------

/// `U = {1..=8}`; `member` and `index` are the two conventions over it (the
/// shipped miscompile's axis — see typed_value_model_coverage.rs).
struct Seed {
    module: Module,
    i64_ty: TyId,
    member: PredId,
    index: PredId,
}

fn seed(name: &str) -> Seed {
    let mut module = Module::new(name);
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
    let index = module
        .intern_pred(Pred::InUniverse(u, Space::Index))
        .expect("Module::intern_pred: test fixture")
        .expect("in range");
    Seed {
        module,
        i64_ty,
        member,
        index,
    }
}

/// `enum E { a(lanes[0]), b(lanes[1]), .. }` (each variant one field), and
/// `fn f(e: E, k: <value_ty>) { <inst>; ret }`.
fn refined_enum_fixture(mut module: Module, lanes: Vec<Ty>, value_ty: Ty, inst: Inst) -> Module {
    let e = Ty::Enum(EnumId::new(0));
    let ft = module
        .add_func_type(FuncTy {
            params: vec![e.clone(), value_ty.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), e));
    b.params.push((ValueId::new(1), value_ty));
    b.body
        .push(InstrNode::new(inst).with_results(vec![ValueId::new(2)]));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    let variants = lanes
        .into_iter()
        .enumerate()
        .map(|(i, ty)| EnumVariant {
            name: ["a", "b", "c"][i].into(),
            fields: vec![ty],
            field_names: vec![],
        })
        .collect();
    module.add_enum(EnumDef::new(EnumId::new(0), "E", variants));
    module
}

fn write_lane1() -> Inst {
    Inst::InsertField {
        ty: Ty::Enum(EnumId::new(0)),
        aggregate: ValueId::new(0),
        field: 1,
        value: ValueId::new(1),
    }
}

fn read_lane1(declared: Ty) -> Inst {
    Inst::ExtractField {
        ty: declared,
        aggregate: ValueId::new(0),
        field: 1,
    }
}

fn not_implied(errors: &[ValidationError]) -> Vec<(&str, &str, &str)> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::RefinementNotImplied {
                location,
                actual,
                required,
            } => Some((location.as_str(), actual.as_str(), required.as_str())),
            _ => None,
        })
        .collect()
}

/// A refined enum lane WRITE is decided by the consumption rule, exactly as a
/// refined struct field write is: one variant, an index carrier offered to a
/// member lane, fires ONE `RefinementNotImplied` naming both predicates, at
/// the struct path's location form.
#[test]
fn a_refined_enum_lane_write_is_checked() {
    let s = seed("ew");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);
    let carrier = Ty::Refine(i64_ty, index);
    let defect = refined_enum_fixture(
        s.module,
        vec![Ty::Refine(i64_ty, member)],
        carrier.clone(),
        write_lane1(),
    );
    let errors = validate_module(&defect);
    assert_eq!(errors.len(), 1, "{}", render(&errors));
    let hits = not_implied(&errors);
    assert_eq!(hits.len(), 1, "{}", render(&errors));
    let (location, actual, required) = hits[0];
    assert!(
        location.ends_with("insert_field enum.0 field 1"),
        "{location}"
    );
    assert!(actual.contains("index into 1..=8"), "{actual}");
    assert!(required.contains("member of 1..=8"), "{required}");

    // PERTURBATION: the lane's own convention is admitted.
    let s = seed("ew_ok");
    let (i64_ty, index) = (s.i64_ty, s.index);
    let carrier = Ty::Refine(i64_ty, index);
    let ok = refined_enum_fixture(
        s.module,
        vec![Ty::Refine(i64_ty, index)],
        carrier.clone(),
        write_lane1(),
    );
    assert_clean(&ok, "index carrier -> index lane");
}

/// The lane requirement is the SET of variant lane types: an index carrier is
/// admitted when SOME variant's lane is an index lane (existential — which
/// variant is active is the dynamic residue), and refused, once PER
/// candidate variant and naming each, when none is.
#[test]
fn an_enum_lane_write_is_admitted_by_some_variant_or_refused_per_variant() {
    let s = seed("ew2_ok");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);
    let carrier = Ty::Refine(i64_ty, index);
    let ok = refined_enum_fixture(
        s.module,
        vec![Ty::Refine(i64_ty, member), Ty::Refine(i64_ty, index)],
        carrier.clone(),
        write_lane1(),
    );
    assert_clean(&ok, "index carrier -> {a: member, b: index}");

    let s = seed("ew2_bad");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);
    let carrier = Ty::Refine(i64_ty, index);
    let bad = refined_enum_fixture(
        s.module,
        vec![Ty::Refine(i64_ty, member), Ty::Refine(i64_ty, member)],
        carrier.clone(),
        write_lane1(),
    );
    let errors = validate_module(&bad);
    let hits = not_implied(&errors);
    assert_eq!(errors.len(), 2, "{}", render(&errors));
    assert_eq!(hits.len(), 2, "{}", render(&errors));
    assert!(hits[0].0.ends_with("(as variant 'a')"), "{}", hits[0].0);
    assert!(hits[1].0.ends_with("(as variant 'b')"), "{}", hits[1].0);
}

/// A READ can narrow: the reader may only assume what some variant's lane
/// establishes. A member lane read as an index is refused; read at its own
/// convention (or unrefined) it is clean.
#[test]
fn a_refined_enum_lane_read_is_checked() {
    let s = seed("er");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);
    let defect = refined_enum_fixture(
        s.module,
        vec![Ty::Refine(i64_ty, member)],
        Ty::U64,
        read_lane1(Ty::Refine(i64_ty, index)),
    );
    let errors = validate_module(&defect);
    let hits = not_implied(&errors);
    assert_eq!(errors.len(), 1, "{}", render(&errors));
    assert_eq!(hits.len(), 1, "{}", render(&errors));
    assert!(
        hits[0].0.ends_with("extract_field enum.0 field 1"),
        "{}",
        hits[0].0
    );
    assert!(hits[0].1.contains("member of 1..=8"), "{}", hits[0].1);
    assert!(hits[0].2.contains("index into 1..=8"), "{}", hits[0].2);

    for declared in ["member", "bare"] {
        let s = seed("er_ok");
        let (i64_ty, member) = (s.i64_ty, s.member);
        let ty = if declared == "member" {
            Ty::Refine(i64_ty, member)
        } else {
            Ty::I64
        };
        let ok = refined_enum_fixture(
            s.module,
            vec![Ty::Refine(i64_ty, member)],
            Ty::U64,
            read_lane1(ty),
        );
        assert_clean(&ok, &format!("member lane read as {declared}"));
    }

    // A refinement over the WRONG representation is not "some variant's
    // lane": it reaches the consumption rule and is refused there, never
    // admitted by the equality half's deferral.
    let s = seed("er_repr");
    let (i64_ty, member) = (s.i64_ty, s.member);
    let wrong_repr = refined_enum_fixture(
        s.module,
        vec![Ty::Ptr],
        Ty::U64,
        read_lane1(Ty::Refine(i64_ty, member)),
    );
    let errors = validate_module(&wrong_repr);
    assert!(
        errors.iter().any(
            |e| matches!(e, ValidationError::RefinementTypeInvalid { location, .. }
                if location.ends_with("extract_field enum.0 field 1"))
        ),
        "{}",
        render(&errors)
    );
}

// ---------------------------------------------------------------------------
// Review twins: the two routes around the equality half
// ---------------------------------------------------------------------------

/// The equality half DEFERS every refined declared type to the consumption
/// rule ("decided by the consumption rule" is true for any lane once the
/// reader's type is a `Refine`), so a refinement over a representation that
/// NO variant carries at that lane must be refused there — never slip through
/// the gap between the two halves. Tree's lanes are unrefined (`u64` / `ptr`);
/// a reader declaring lane 1 as `Refine(i64, member)` and a writer offering a
/// `Refine(i64, member)` value to lane 2 are each refused with the named
/// `RefinementTypeInvalid`, once per candidate variant, from both entry
/// points.
#[test]
fn a_refinement_over_no_variants_representation_is_refused() {
    let tree_probe = |value_ty: Ty, inst: Inst, s: Seed| {
        let mut m = s.module;
        let ft = m
            .add_func_type(FuncTy {
                params: vec![tree(), value_ty.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(0), "probe", ft, BlockId::new(0));
        // Licensed, so the codegen entry point reports only the lane refusals.
        f.body_gate = Some(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let mut b = Block::new(BlockId::new(0));
        b.params.push((ValueId::new(0), tree()));
        b.params.push((ValueId::new(1), value_ty));
        b.body
            .push(InstrNode::new(inst).with_results(vec![ValueId::new(2)]));
        b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(b);
        m.functions.push(f);
        m.add_enum(tree_def(None));
        m
    };
    let type_invalid = |errors: &[ValidationError]| -> Vec<String> {
        errors
            .iter()
            .filter_map(|e| match e {
                ValidationError::RefinementTypeInvalid { location, .. } => Some(location.clone()),
                _ => None,
            })
            .collect()
    };

    // READ: lane 1 is `u64` (leaf) or `ptr` (node) — an i64 refinement is
    // over neither, so both candidates refuse, each naming its variant.
    let s = seed("rv_read");
    let refined = Ty::Refine(s.i64_ty, s.member);
    let read = tree_probe(
        Ty::U64,
        Inst::ExtractField {
            ty: refined,
            aggregate: ValueId::new(0),
            field: 1,
        },
        s,
    );
    for (entry, errors) in [
        ("validate_module", validate_module(&read)),
        (
            "validate_module_for_codegen",
            validate_module_for_codegen(&read),
        ),
    ] {
        let hits = type_invalid(&errors);
        assert_eq!(errors.len(), 2, "{entry}: {}", render(&errors));
        assert_eq!(hits.len(), 2, "{entry}: {}", render(&errors));
        assert!(
            hits[0].ends_with("(as variant 'leaf')"),
            "{entry}: {}",
            hits[0]
        );
        assert!(
            hits[1].ends_with("(as variant 'node')"),
            "{entry}: {}",
            hits[1]
        );
    }

    // WRITE: lane 2 exists only on `node`, at `ptr`; one candidate, so the
    // location is the struct path's form.
    let s = seed("rv_write");
    let refined = Ty::Refine(s.i64_ty, s.member);
    let write = tree_probe(
        refined,
        Inst::InsertField {
            ty: tree(),
            aggregate: ValueId::new(0),
            field: 2,
            value: ValueId::new(1),
        },
        s,
    );
    let errors = validate_module(&write);
    let hits = type_invalid(&errors);
    assert_eq!(errors.len(), 1, "{}", render(&errors));
    assert_eq!(hits.len(), 1, "{}", render(&errors));
    assert!(
        hits[0].ends_with("insert_field enum.0 field 2"),
        "{}",
        hits[0]
    );
}

/// An enum id with no definition is refused like every other aggregate's
/// dangling id, never treated as "no lanes to check".
#[test]
fn a_lane_access_on_an_undefined_enum_is_refused() {
    let mut m = extract(Ty::U64, 1);
    m.enums.clear();
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::FieldAccessInvalid { op, reason, .. }
                if op == "extract_field" && reason.contains("references an undefined definition")
        )),
        "{}",
        render(&errors)
    );
    assert!(
        !errors
            .iter()
            .any(|e| matches!(e, ValidationError::OperandTypeMismatch { .. })),
        "a dangling enum has no lane model to report a lane type against: {}",
        render(&errors)
    );
}

/// `insert_field` on lane 0 is refused at EVERY value type, the canonical tag
/// type included: a re-tag keeps the old variant's payload lanes under the new
/// tag. Two modules: ONE change to the well-formed Tree module
/// (`clean_mk_leaf` re-tags its `leaf` as a `node`), which the interpreter
/// catches only later and only by arity; and the c06 `p1_insert_tag_overwrite`
/// shape (equal arity), which the interpreter runs to `Ok`, so the validator
/// is the only line that sees it.
#[test]
fn a_tag_lane_write_is_refused_at_every_type() {
    for ty in [Ty::U8, Ty::U64, Ty::I8] {
        assert_one_refusal(
            &validate_module(&insert(tree(), 0, ty.clone())),
            &format!("insert tag value {ty}"),
            "insert_field",
            Want::Invalid("insert_field cannot rewrite an enum discriminant"),
        );
    }
    // The result-type rule still fires alongside, as for every aggregate.
    let errors = validate_module(&insert(Ty::U8, 0, Ty::U8));
    assert_eq!(errors.len(), 2, "{}", render(&errors));
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { role, .. } if role == "result"
        )),
        "{}",
        render(&errors)
    );

    let m = build_tree(Some(tree_direct_layout()));
    let mut retag = m.clone();
    let f = retag
        .functions
        .iter_mut()
        .find(|f| f.name == "clean_mk_leaf")
        .expect("clean_mk_leaf");
    // Two fresh ids past every value the function already defines.
    let next = f
        .blocks
        .iter()
        .flat_map(|b| {
            b.params.iter().map(|(v, _)| v.index()).chain(
                b.body
                    .iter()
                    .flat_map(|n| n.results.iter().map(|v| v.index())),
            )
        })
        .max()
        .map_or(0, |m| m + 1);
    let (t, re) = (ValueId::new(next), ValueId::new(next + 1));
    let entry = &mut f.blocks[0];
    let ret = entry.body.pop().expect("return");
    // %t  = u8 1
    // %re = insert_field tree %out, 0, %t     -- re-tag the leaf as a node
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(1),
        })
        .with_results(vec![t]),
    );
    let Inst::Return { values } = &ret.inst else {
        panic!("clean_mk_leaf ends in a return")
    };
    let out = values[0];
    entry.body.push(
        InstrNode::new(Inst::InsertField {
            ty: tree(),
            aggregate: out,
            field: 0,
            value: t,
        })
        .with_results(vec![re]),
    );
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![re] }));
    let errors = validate_module_for_codegen(&retag);
    assert_one_refusal(
        &errors,
        "re-tag leaf as node in clean_mk_leaf",
        "insert_field",
        Want::Invalid("construct the variant with Const"),
    );
    // The interpreter refuses the insert itself (WS2.2 item 5, mirroring
    // Lean's `semInsertField`). Before it, the re-tag ran and tripped only at
    // the next whole-enum Store, and only because the arities differ.
    let run = run_nullary(&retag, "program");
    assert!(
        matches!(&run, Err(e) if e.starts_with("UndefinedBehavior")
            && e.contains("insert_field cannot rewrite an enum discriminant")),
        "the re-tag is refused where it happens: {run:?}"
    );

    // With EQUAL arity nothing downstream notices (c06 `p1_insert_tag_overwrite`):
    // `enum E { a(u64), b(u64) }`, an `a(7)` re-tagged as `b` used to run to
    // Ok 7. Both lines now refuse it: the validator statically, the
    // interpreter at the insert.
    let e = Ty::Enum(EnumId::new(0));
    let mut same = Module::new("c06_retag_same_arity");
    let ft = same
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "program", ft, BlockId::new(0));
    f.body_gate = Some(BodyGate::Gated {
        authority: "trust-verify".into(),
        evidence: None,
    });
    let mut b = Block::new(BlockId::new(0));
    b.body.push(
        InstrNode::new(Inst::Const {
            ty: e.clone(),
            value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(7)]),
        })
        .with_results(vec![ValueId::new(0)]),
    );
    b.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(1),
        })
        .with_results(vec![ValueId::new(1)]),
    );
    b.body.push(
        InstrNode::new(Inst::InsertField {
            ty: e.clone(),
            aggregate: ValueId::new(0),
            field: 0,
            value: ValueId::new(1),
        })
        .with_results(vec![ValueId::new(2)]),
    );
    b.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U64,
            aggregate: ValueId::new(2),
            field: 1,
        })
        .with_results(vec![ValueId::new(3)]),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3)],
    }));
    f.blocks.push(b);
    same.functions.push(f);
    same.add_enum(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "a".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
            EnumVariant {
                name: "b".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
        ],
    ));
    let run = run_nullary(&same, "program");
    assert!(
        matches!(&run, Err(e) if e.starts_with("UndefinedBehavior")
            && e.contains("insert_field cannot rewrite an enum discriminant (lane 0 of enum.0)")),
        "the equal-arity re-tag no longer runs silently: {run:?}"
    );
    assert_one_refusal(
        &validate_module_for_codegen(&same),
        "re-tag a(7) as b",
        "insert_field",
        Want::Invalid("insert_field cannot rewrite an enum discriminant"),
    );
}

// ---------------------------------------------------------------------------
// The roadmap WS2.2 fixture, verbatim: `enum AB { A(i64), B(ptr) }`
// ---------------------------------------------------------------------------

fn ab_def() -> EnumDef {
    EnumDef::new(
        EnumId::new(0),
        "AB",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::I64],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![Ty::Ptr],
                field_names: vec![],
            },
        ],
    )
}

fn ab() -> Ty {
    Ty::Enum(EnumId::new(0))
}

/// `fn program() -> <ret> { %e = const AB [disc, payload]; <proj of %e>; ret }`.
/// `proj` is ONE `ExtractField` over `%e` (value 0); its result is value 1.
fn ab_program(disc: i128, payload: Constant, ret: Ty, proj: Inst) -> Module {
    let mut m = Module::new("ws22_ab");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![ret],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "program", ft, BlockId::new(0));
    f.body_gate = Some(BodyGate::Gated {
        authority: "trust-verify".into(),
        evidence: None,
    });
    let mut b = Block::new(BlockId::new(0));
    b.body.push(
        InstrNode::new(Inst::Const {
            ty: ab(),
            value: Constant::Aggregate(vec![Constant::Int(disc), payload]),
        })
        .with_results(vec![ValueId::new(0)]),
    );
    b.body
        .push(InstrNode::new(proj).with_results(vec![ValueId::new(1)]));
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    f.blocks.push(b);
    m.functions.push(f);
    m.add_enum(ab_def());
    m
}

fn extract_e(ty: Ty, field: u32) -> Inst {
    Inst::ExtractField {
        ty,
        aggregate: ValueId::new(0),
        field,
    }
}

/// `fn probe(e: AB, x: <value_ty>) { %r = <inst>; ret }` over `AB`.
fn ab_probe(value_ty: Ty, inst: Inst) -> Module {
    let mut m = probe(value_ty, inst);
    m.enums.clear();
    m.add_enum(ab_def());
    m
}

/// POSITIVE: `extract_field i64 %e, 1` on an `A` value and `extract_field u8
/// %e, 0` validate (also for codegen) and run to the payload / the tag.
#[test]
fn ws22_positive_payload_and_tag_reads_validate_and_run() {
    let payload = ab_program(0, Constant::Int(-5), Ty::I64, extract_e(Ty::I64, 1));
    assert_clean(&payload, "extract_field i64 %e, 1");
    assert!(validate_module_for_codegen(&payload).is_empty());
    let got = run_nullary(&payload, "program").expect("A(-5).0 runs");
    assert_eq!(got[0].as_int().map(|i| i.as_signed()), Some(-5));

    for (disc, payload) in [(0, Constant::Int(9)), (1, Constant::Int(0))] {
        let tag = ab_program(disc, payload.clone(), Ty::U8, extract_e(Ty::U8, 0));
        assert_clean(&tag, "extract_field u8 %e, 0");
        let got = run_nullary(&tag, "program").expect("tag read runs");
        assert_eq!(got[0].as_int().map(|i| i.as_unsigned()), Some(disc as u128));
    }
}

/// NEGATIVE TWINS, one per rule, each ONE mutation of an accepted probe and
/// each refused with its named reason.
#[test]
fn ws22_negative_twins_are_refused_with_named_reasons() {
    // Accepted baselines the twins mutate.
    assert_clean(&ab_probe(Ty::U64, extract_e(Ty::I64, 1)), "lane 1 as i64");
    assert_clean(&ab_probe(Ty::U64, extract_e(Ty::U8, 0)), "lane 0 as u8");
    let insert_ab = |result: Ty, field: u32, value_ty: Ty| {
        ab_probe(
            value_ty,
            Inst::InsertField {
                ty: result,
                aggregate: ValueId::new(0),
                field,
                value: ValueId::new(1),
            },
        )
    };
    assert_clean(&insert_ab(ab(), 1, Ty::I64), "insert i64 into lane 1");

    // lane 99
    assert_one_refusal(
        &validate_module(&ab_probe(Ty::U64, extract_e(Ty::I64, 99))),
        "lane 99",
        "extract_field",
        Want::Invalid("field 99 is out of range for every variant of enum.0"),
    );
    // lane 1 as f64
    assert_one_refusal(
        &validate_module(&ab_probe(Ty::U64, extract_e(Ty::F64, 1))),
        "lane 1 as f64",
        "extract_field",
        mismatch("field", "one of {A: i64, B: ptr}", &Ty::F64),
    );
    // lane 0 as u64 (the tag is u8)
    assert_one_refusal(
        &validate_module(&ab_probe(Ty::U64, extract_e(Ty::U64, 0))),
        "lane 0 as u64",
        "extract_field",
        mismatch("field", "u8", &Ty::U64),
    );
    // insert_field lane 0
    assert_one_refusal(
        &validate_module(&insert_ab(ab(), 0, Ty::U8)),
        "insert_field lane 0",
        "insert_field",
        Want::Invalid(
            "insert_field cannot rewrite an enum discriminant; construct the variant with Const",
        ),
    );
    // an `insert_field i64 <enum>` result
    assert_one_refusal(
        &validate_module(&insert_ab(Ty::I64, 1, Ty::I64)),
        "insert_field i64 <enum>",
        "insert_field",
        mismatch("result", "enum.0", &Ty::I64),
    );
    // inserting an f64 into lane 1
    assert_one_refusal(
        &validate_module(&insert_ab(ab(), 1, Ty::F64)),
        "insert f64 into lane 1",
        "insert_field",
        mismatch("value", "one of {A: i64, B: ptr}", &Ty::F64),
    );
}

/// MUTATION CONTROL (the static/dynamic split): `B` has `ptr` at lane 1, so
/// `extract_field ptr %e, 1` validates — a rule that refused every
/// multi-variant lane would break the positive fixture — and on an `A` value
/// the interpreter returns `UndefinedBehavior`, naming the active variant.
#[test]
fn mutation_control_wrong_variant_lane_validates_and_is_ub_at_run_time() {
    let wrong = ab_program(0, Constant::Int(7), Ty::Ptr, extract_e(Ty::Ptr, 1));
    assert_clean(&wrong, "extract_field ptr %e, 1 (B's lane) off an A value");
    assert!(validate_module_for_codegen(&wrong).is_empty());
    let run = run_nullary(&wrong, "program");
    assert!(
        matches!(&run, Err(e) if e.starts_with("UndefinedBehavior")
            && e.contains("enum enum.0: lane 1 belongs to no field of active variant A")),
        "{run:?}"
    );
    // The same read off a `B` value is fine: the check is the ACTIVE variant.
    let right = ab_program(1, Constant::Int(0), Ty::Ptr, extract_e(Ty::Ptr, 1));
    assert_clean(&right, "B's lane off a B value");
    // A null-address `Const` ptr payload: the read itself succeeds.
    assert!(run_nullary(&right, "program").is_ok());
}

/// STRUCT CONTROL: the struct path's refusals are unchanged by the enum arm —
/// an out-of-range struct field is still `FieldAccessInvalid` with the
/// struct wording, and an in-range field at the wrong type is still a
/// `field` mismatch naming the one field type.
#[test]
fn struct_control_field_access_refusals_are_unchanged() {
    let mut mb = ModuleBuilder::new("ws22_struct_control");
    let sid = mb.add_struct(trust_ir::ty::StructDef {
        id: trust_ir::StructId::new(0),
        name: "S".into(),
        fields: vec![trust_ir::ty::FieldDef {
            name: "x".into(),
            ty: Ty::I64,
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    let s_ty = Ty::Struct(sid);
    let ft = mb.add_func_type(vec![s_ty.clone()], vec![]);
    {
        let mut fb = mb.function("probe", ft);
        let entry = fb.create_block();
        let s = fb.add_block_param(entry, s_ty.clone());
        fb.switch_to_block(entry);
        fb.extract_field(Ty::I64, s, 1);
        fb.ret(vec![]);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_one_refusal(
        &validate_module(&m),
        "struct field 1 of a one-field struct",
        "extract_field",
        Want::Invalid("field index 1 is out of range for struct.0 (1 fields)"),
    );
}

/// An enum with NO canonical tag repr (here uninhabited: zero variants) has no
/// lanes: EVERY projection is refused, the tag lane and payload lanes alike,
/// never waved through for want of a lane model.
#[test]
fn an_enum_without_a_canonical_tag_refuses_every_projection() {
    for (field, ty) in [(0, Ty::U8), (1, Ty::U64)] {
        let mut m = extract(ty.clone(), field);
        m.enums[0].variants.clear();
        assert!(m.enums[0].canonical_tag_repr().is_none());
        let errors = validate_module(&m);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::FieldAccessInvalid { op, reason, .. }
                    if op == "extract_field"
                        && reason.contains("has no canonical tag repr (uninhabited or \
                                            unrepresentable), so no lane of it can be projected")
            )),
            "lane {field}: {}",
            render(&errors)
        );
    }
}

/// HONEST LIMIT (WS2.2 item 4): a wrong-variant projection whose lane has the
/// SAME type in both variants is undetectable by either engine — the flat
/// form carries no statement of the expected variant. `enum E { A(i64),
/// B(i64) }`, lane 1 read off a `B` value by code that means `A`: it validates
/// and runs to `Ok`. Only the variant-indexed projection (DECIDE (a), a
/// reserved wire version) closes it; when it lands, this row flips.
#[test]
fn honest_limit_same_typed_wrong_variant_lane_is_invisible() {
    let mut m = ab_program(1, Constant::Int(11), Ty::I64, extract_e(Ty::I64, 1));
    m.enums[0].variants[1].fields = vec![Ty::I64];
    assert_clean(&m, "lane 1 of a B value read as A's i64");
    let got = run_nullary(&m, "program").expect("indistinguishable, so it runs");
    assert_eq!(got[0].as_int().map(|i| i.as_signed()), Some(11));
}
