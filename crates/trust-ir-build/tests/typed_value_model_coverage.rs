// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// WP-1B/G1 — CONSUMPTION COVERAGE, and its mechanical completeness gate.
// ══════════════════════════════════════════════════════════════════════════
//
// WP-1 fired the consumption rule at call arguments, `Invoke` arguments,
// returns, control-flow join edges and entry parameters. It did NOT fire at:
//
//   * a `Store` into a refined LOCATION,
//   * a `CallIndirect` against its DECLARED signature,
//   * a refined struct / record / array / frame-slot FIELD write — or read.
//
// A frontend emitting any of those got SILENCE, which is a hole in exactly the
// mechanism this model exists to be. This file closes each one in the
// two-sided style the campaign requires:
//
//   (a) a DEFECT module that fires EXACTLY ONE error, of the right variant, at
//       the right site, naming both predicates; and
//   (b) a PERTURBATION of the same module along the one axis that carries the
//       defect — still well-formed, still fully refined, still exercising the
//       same instruction — which must produce ZERO errors from the WHOLE
//       validator.
//
// Plus the mechanical gate: `consumption_role` is exhaustive over `Inst` with
// no wildcard arm, so a future instruction is a COMPILE error rather than a
// silent hole, and `every_instruction_has_a_stated_consumption_role` asserts
// the classification is populated rather than merely present.

use trust_ir::inst::{BinOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FieldDef, RecordDef, StructDef};
use trust_ir::value::{
    BlockId, FuncId, FuncTyId, PredId, RecordId, StructId, TyId, UnivId, ValueId,
};
use trust_ir::{Block, Constant, FuncTy, Function, Module, Pred, Space, Ty, Universe};
use trust_ir_build::{
    CheckedConsumption, ConsumptionRole, ValidationError, consumption_role, validate_module,
};

/// `U = {1..=8}` — the union-key universe from the shipped miscompile. A valid
/// INDEX into it is `0..=7`; a valid MEMBER is `1..=8`. Every fixture below
/// uses that one-element gap as its defect axis.
const M: i128 = 8;

// ---------------------------------------------------------------------------
// Assertion helpers
// ---------------------------------------------------------------------------

fn render(errors: &[ValidationError]) -> String {
    errors
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join(" | ")
}

/// ZERO errors from the whole validator — the non-vacuity anchor.
fn assert_clean(module: &Module, what: &str) {
    let errors = validate_module(module);
    assert!(
        errors.is_empty(),
        "{what} must validate clean, got {} error(s): {}",
        errors.len(),
        render(&errors)
    );
}

/// Exactly one `RefinementNotImplied`, at `site`, naming BOTH predicates.
fn assert_one_named_failure(
    module: &Module,
    what: &str,
    site_fragment: &str,
    actual_fragment: &str,
    required_fragment: &str,
) {
    let errors = validate_module(module);
    assert_eq!(
        errors.len(),
        1,
        "{what}: expected exactly one error, got {}: {}",
        errors.len(),
        render(&errors)
    );
    let ValidationError::RefinementNotImplied {
        location,
        actual,
        required,
    } = &errors[0]
    else {
        panic!("{what}: expected RefinementNotImplied, got {:?}", errors[0]);
    };
    assert!(
        location.contains(site_fragment),
        "{what}: expected site {site_fragment:?}, got {location:?}"
    );
    assert!(
        actual.contains(actual_fragment),
        "{what}: the carried predicate must be NAMED; expected {actual_fragment:?} in {actual:?}"
    );
    assert!(
        required.contains(required_fragment),
        "{what}: the required predicate must be NAMED; expected {required_fragment:?} in \
         {required:?}"
    );
}

// ---------------------------------------------------------------------------
// Shared module scaffolding
// ---------------------------------------------------------------------------

/// A module seeded with `U = 1..=8` and the two carriers over it.
struct Seed {
    module: Module,
    i64_ty: TyId,
    member: PredId,
    index: PredId,
}

fn seed(name: &str) -> Seed {
    let mut module = Module::new(name);
    let i64_ty = module.add_type(Ty::I64);
    let u = module
        .intern_universe(Universe::IntRange { lo: 1, hi: M })
        .expect("canonical");
    let member = module
        .intern_pred(Pred::InUniverse(u, Space::Member))
        .expect("in range");
    let index = module
        .intern_pred(Pred::InUniverse(u, Space::Index))
        .expect("in range");
    let _ = UnivId::new(0);
    Seed {
        module,
        i64_ty,
        member,
        index,
    }
}

// ---------------------------------------------------------------------------
// SITE 1 — `Store` into a refined LOCATION
// ---------------------------------------------------------------------------

/// ```text
/// fn writer(k: refine<i64, carrier>) {
///   %p = alloca i64
///   store <location_ty> %p, %k
///   ret
/// }
/// ```
///
/// `Store.ty` is the LOCATION's type, not this instruction's own result type —
/// it is the contract a later `Load` reads back, so it is declared for one
/// instruction and consumed by another. A value that does not satisfy it puts
/// the wrong convention in memory, and every reader downstream inherits it.
fn store_fixture(name: &str, carrier: PredId, location_ty: Ty, seed: Seed) -> Module {
    let Seed {
        mut module, i64_ty, ..
    } = seed;
    let _ = name;
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Refine(i64_ty, carrier)],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "writer", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params
        .push((ValueId::new(0), Ty::Refine(i64_ty, carrier)));
    b.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        })
        .with_results(vec![ValueId::new(1)]),
    );
    b.body.push(InstrNode::new(Inst::Store {
        ty: location_ty,
        ptr: ValueId::new(1),
        value: ValueId::new(0),
        volatile: false,
        align: None,
    }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

#[test]
fn store_into_a_refined_location_is_checked() {
    // ── DEFECT: an INDEX carrier stored into a MEMBER location ────────────
    let s = seed("store_defect");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);
    let defect = store_fixture(
        "store_defect",
        index,
        Ty::Refine(i64_ty, member),
        seed("store_defect"),
    );
    assert_one_named_failure(
        &defect,
        "DEFECT: index carrier -> member location",
        "store value",
        "index into 1..=8",
        "member of 1..=8",
    );

    // ── PERTURBATION: flip the LOCATION's convention, nothing else ────────
    // Same value, same universe, same machine word, same `Store`, refinement
    // machinery still fully live — only what the location demands moved. If
    // the defect above fired for any reason other than the convention, this
    // would still fail.
    let ok = store_fixture(
        "store_perturbed",
        index,
        Ty::Refine(i64_ty, index),
        seed("store_perturbed"),
    );
    assert_clean(&ok, "PERTURBATION: index carrier -> index location");

    // ── PERTURBATION: the location demands nothing ────────────────────────
    let ok = store_fixture("store_bare", index, Ty::I64, seed("store_bare"));
    assert_clean(&ok, "PERTURBATION: index carrier -> unrefined location");

    // ── BASELINE: the same program with no refinements at all ─────────────
    let mut bare = Module::new("store_baseline");
    let i64_ty = bare.add_type(Ty::I64);
    let _ = i64_ty;
    let ft = bare.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "writer", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::I64));
    b.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        })
        .with_results(vec![ValueId::new(1)]),
    );
    b.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I64,
        ptr: ValueId::new(1),
        value: ValueId::new(0),
        volatile: false,
        align: None,
    }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    bare.functions.push(f);
    assert_clean(&bare, "BASELINE: the unrefined store (this is what ships)");
}

// ---------------------------------------------------------------------------
// SITE 2 — `CallIndirect` against a DECLARED signature
// ---------------------------------------------------------------------------

/// ```text
/// fn caller(fp: ptr, k: refine<i64, carrier>) {
///   call_indirect fp : functy.N (k)
///   ret
/// }
/// ```
///
/// An indirect call has no statically-known callee, so the `sig` it DECLARES
/// is the entire contract the backend lowers the edge against. It is exactly
/// as load-bearing as a direct callee's signature, and it was unchecked.
fn call_indirect_fixture(carrier: PredId, sig_param: Ty, seed: Seed) -> Module {
    let Seed {
        mut module, i64_ty, ..
    } = seed;
    let sig = module.add_func_type(FuncTy {
        params: vec![sig_param],
        returns: vec![],
        is_vararg: false,
    });
    let caller_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Refine(i64_ty, carrier)],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "caller", caller_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::Ptr));
    b.params
        .push((ValueId::new(1), Ty::Refine(i64_ty, carrier)));
    b.body.push(InstrNode::new(Inst::CallIndirect {
        callee: ValueId::new(0),
        sig,
        args: vec![ValueId::new(1)],
        calling_conv: trust_ir::CallingConv::C,
    }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

#[test]
fn call_indirect_against_its_declared_signature_is_checked() {
    let s = seed("ci");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);

    // ── DEFECT ────────────────────────────────────────────────────────────
    let defect = call_indirect_fixture(index, Ty::Refine(i64_ty, member), seed("ci_defect"));
    assert_one_named_failure(
        &defect,
        "DEFECT: index carrier -> member signature param",
        "call_indirect functy.0 arg 0",
        "index into 1..=8",
        "member of 1..=8",
    );

    // ── PERTURBATION: flip the SIGNATURE's convention ─────────────────────
    let ok = call_indirect_fixture(index, Ty::Refine(i64_ty, index), seed("ci_ok"));
    assert_clean(&ok, "PERTURBATION: index carrier -> index signature param");

    // ── PERTURBATION: a strictly STRONGER carrier is accepted ─────────────
    // Proving the check is entailment, not predicate equality.
    let mut s = seed("ci_sub");
    let sub = s
        .module
        .intern_in_universe(Universe::IntRange { lo: 2, hi: 5 }, Space::Member)
        .expect("canonical");
    let member = s.member;
    let i64_ty = s.i64_ty;
    let ok = call_indirect_fixture(sub, Ty::Refine(i64_ty, member), s);
    assert_clean(&ok, "PERTURBATION: member of 2..=5 -> member of 1..=8");
}

// ---------------------------------------------------------------------------
// SITE 3 — refined FIELD write (struct / record) and FIELD read
// ---------------------------------------------------------------------------

/// ```text
/// struct @Row { key: <field_ty> }
/// fn write(agg: @Row, k: refine<i64, carrier>) { insert_field @Row agg, 0, k; ret }
/// ```
fn field_write_fixture(carrier: PredId, field_ty: Ty, seed: Seed) -> Module {
    let Seed {
        mut module, i64_ty, ..
    } = seed;
    let row = StructId::new(0);
    module.add_struct(StructDef {
        id: row,
        name: "Row".into(),
        fields: vec![FieldDef {
            name: "key".into(),
            ty: field_ty,
            offset: None,
        }],
        size: None,
        align: None,
        repr: trust_ir::ty::StructRepr::Rust,
    });
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Struct(row), Ty::Refine(i64_ty, carrier)],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "write", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::Struct(row)));
    b.params
        .push((ValueId::new(1), Ty::Refine(i64_ty, carrier)));
    b.body.push(
        InstrNode::new(Inst::InsertField {
            ty: Ty::Struct(row),
            aggregate: ValueId::new(0),
            field: 0,
            value: ValueId::new(1),
        })
        .with_results(vec![ValueId::new(2)]),
    );
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

#[test]
fn a_refined_struct_field_write_is_checked() {
    let s = seed("fw");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);

    // ── DEFECT ────────────────────────────────────────────────────────────
    let defect = field_write_fixture(index, Ty::Refine(i64_ty, member), seed("fw_defect"));
    assert_one_named_failure(
        &defect,
        "DEFECT: index carrier -> member field",
        "insert_field",
        "index into 1..=8",
        "member of 1..=8",
    );

    // ── PERTURBATION: flip the FIELD's convention ─────────────────────────
    let ok = field_write_fixture(index, Ty::Refine(i64_ty, index), seed("fw_ok"));
    assert_clean(&ok, "PERTURBATION: index carrier -> index field");

    // ── PERTURBATION: an unrefined field demands nothing ──────────────────
    let ok = field_write_fixture(index, Ty::I64, seed("fw_bare"));
    assert_clean(&ok, "PERTURBATION: index carrier -> unrefined field");
}

/// The RECORD spelling of the same defect. `Record` is a distinct definition
/// table from `Struct`, so covering one does not cover the other.
#[test]
fn a_refined_record_field_write_is_checked() {
    fn build(carrier: PredId, field_ty: Ty, seed: Seed) -> Module {
        let Seed {
            mut module, i64_ty, ..
        } = seed;
        let rec = RecordId::new(0);
        module.add_record(RecordDef {
            id: rec,
            name: "Row".into(),
            fields: vec![FieldDef {
                name: "key".into(),
                ty: field_ty,
                offset: None,
            }],
        });
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Record(rec), Ty::Refine(i64_ty, carrier)],
            returns: vec![],
            is_vararg: false,
        });
        let mut f = Function::new(FuncId::new(0), "write", ft, BlockId::new(0));
        let mut b = Block::new(BlockId::new(0));
        b.params.push((ValueId::new(0), Ty::Record(rec)));
        b.params
            .push((ValueId::new(1), Ty::Refine(i64_ty, carrier)));
        b.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Record(rec),
                aggregate: ValueId::new(0),
                field: 0,
                value: ValueId::new(1),
            })
            .with_results(vec![ValueId::new(2)]),
        );
        b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(b);
        module.functions.push(f);
        module
    }

    let s = seed("rw");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);
    let defect = build(index, Ty::Refine(i64_ty, member), seed("rw_defect"));
    assert_one_named_failure(
        &defect,
        "DEFECT: index carrier -> member record field",
        "insert_field",
        "index into 1..=8",
        "member of 1..=8",
    );
    let ok = build(index, Ty::Refine(i64_ty, index), seed("rw_ok"));
    assert_clean(&ok, "PERTURBATION: index carrier -> index record field");
}

/// ```text
/// struct @Row { key: <field_ty> }
/// fn read(agg: @Row) { %v = extract_field <demanded> agg, 0; ret }
/// ```
///
/// **A READ CAN NARROW.** `ExtractField.ty` is what the READER declares the
/// field to be, and nothing structural stops it declaring a stronger
/// refinement than the definition guarantees. That is the entry-parameter
/// direction wearing a different hat — a consumer may only assume what the
/// definition establishes — so the read is a consumption site and the
/// definition's type is the carrier.
fn field_read_fixture(field_ty: Ty, demanded: Ty, seed: Seed) -> Module {
    let Seed { mut module, .. } = seed;
    let row = StructId::new(0);
    module.add_struct(StructDef {
        id: row,
        name: "Row".into(),
        fields: vec![FieldDef {
            name: "key".into(),
            ty: field_ty,
            offset: None,
        }],
        size: None,
        align: None,
        repr: trust_ir::ty::StructRepr::Rust,
    });
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Struct(row)],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "read", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::Struct(row)));
    b.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: demanded,
            aggregate: ValueId::new(0),
            field: 0,
        })
        .with_results(vec![ValueId::new(1)]),
    );
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

#[test]
fn a_refined_field_read_may_not_narrow_what_the_definition_guarantees() {
    let s = seed("fr");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);

    // ── DEFECT: the definition says INDEX, the reader demands MEMBER ──────
    let defect = field_read_fixture(
        Ty::Refine(i64_ty, index),
        Ty::Refine(i64_ty, member),
        seed("fr_defect"),
    );
    assert_one_named_failure(
        &defect,
        "DEFECT: reader narrows an index field to a member",
        "extract_field field 0",
        "index into 1..=8",
        "member of 1..=8",
    );

    // ── DEFECT: an UNREFINED field read as a refined one ──────────────────
    // The commonest shape: the aggregate never recorded the convention, and
    // the reader helps itself to one. Under the old regime this compiled.
    let defect = field_read_fixture(Ty::I64, Ty::Refine(i64_ty, member), seed("fr_top"));
    assert_one_named_failure(
        &defect,
        "DEFECT: reader invents a convention the field never carried",
        "extract_field field 0",
        "top (no refinement carried",
        "member of 1..=8",
    );

    // ── PERTURBATION: the reader asks for exactly what is declared ────────
    let ok = field_read_fixture(
        Ty::Refine(i64_ty, member),
        Ty::Refine(i64_ty, member),
        seed("fr_ok"),
    );
    assert_clean(&ok, "PERTURBATION: reader demands what the field declares");

    // ── PERTURBATION: the reader WIDENS, which is always sound ────────────
    let mut s = seed("fr_widen");
    let numeric = s
        .module
        .intern_pred(Pred::Interval { lo: 0, hi: 9 })
        .expect("canonical");
    let (i64_ty, member) = (s.i64_ty, s.member);
    let ok = field_read_fixture(Ty::Refine(i64_ty, member), Ty::Refine(i64_ty, numeric), s);
    assert_clean(&ok, "PERTURBATION: reader widens a member to its bounds");
}

// ---------------------------------------------------------------------------
// SITE 4 — refined ARRAY element write / read
// ---------------------------------------------------------------------------

/// ```text
/// fn write(a: [4 x <elem>], i: i64, k: refine<i64, carrier>) {
///   %r = insert_element <[4 x elem]> a, i, k ; ret
/// }
/// ```
fn element_write_fixture(carrier: PredId, elem_ty: Ty, seed: Seed) -> Module {
    let Seed {
        mut module, i64_ty, ..
    } = seed;
    let elem_id = module.add_type(elem_ty);
    let array = Ty::Array(elem_id, 4);
    let ft = module.add_func_type(FuncTy {
        params: vec![array.clone(), Ty::I64, Ty::Refine(i64_ty, carrier)],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "write", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), array.clone()));
    b.params.push((ValueId::new(1), Ty::I64));
    b.params
        .push((ValueId::new(2), Ty::Refine(i64_ty, carrier)));
    b.body.push(
        InstrNode::new(Inst::InsertElement {
            ty: array,
            array: ValueId::new(0),
            index: ValueId::new(1),
            value: ValueId::new(2),
        })
        .with_results(vec![ValueId::new(3)]),
    );
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

#[test]
fn a_refined_array_element_write_is_checked() {
    let s = seed("ew");
    let (i64_ty, index, member) = (s.i64_ty, s.index, s.member);

    let defect = element_write_fixture(index, Ty::Refine(i64_ty, member), seed("ew_defect"));
    assert_one_named_failure(
        &defect,
        "DEFECT: index carrier -> member array element",
        "insert_element",
        "index into 1..=8",
        "member of 1..=8",
    );

    let ok = element_write_fixture(index, Ty::Refine(i64_ty, index), seed("ew_ok"));
    assert_clean(&ok, "PERTURBATION: index carrier -> index array element");

    let ok = element_write_fixture(index, Ty::I64, seed("ew_bare"));
    assert_clean(&ok, "PERTURBATION: index carrier -> unrefined element");
}

// ---------------------------------------------------------------------------
// THE MECHANICAL COMPLETENESS GATE
// ---------------------------------------------------------------------------

#[test]
fn every_instruction_has_a_stated_consumption_role() {
    // `consumption_role` is an EXHAUSTIVE match over `Inst` with no wildcard
    // arm, so a new instruction cannot be added to the IR without an author
    // stating which answer applies — that is the compile-time half of this
    // gate, and it is enforced by rustc, not by this test.
    //
    // The runtime half: every `NoDeclaredRequirement` must carry a REASON, so
    // the classification is auditable rather than a silent shrug, and every
    // `Checked` site kind must actually be reachable from some instruction
    // (otherwise the dispatch arm is dead and the coverage claim is a fiction).
    let samples: Vec<Inst> = sample_of_every_instruction();

    let mut reached: Vec<CheckedConsumption> = Vec::new();
    for inst in &samples {
        match consumption_role(inst) {
            ConsumptionRole::Checked(site) => reached.push(site),
            ConsumptionRole::NoDeclaredRequirement(reason) => {
                assert!(
                    reason.len() > 20,
                    "an unchecked position must STATE why, got {reason:?} for {inst:?}"
                );
            }
            ConsumptionRole::ConsumesNoValue => {}
        }
    }
    reached.sort();
    reached.dedup();

    let expected = [
        CheckedConsumption::DirectCallArgs,
        CheckedConsumption::InvokeArgsAndNormalEdge,
        CheckedConsumption::IndirectCallArgs,
        CheckedConsumption::ReturnValues,
        CheckedConsumption::BranchArgs,
        CheckedConsumption::StoreValue,
        CheckedConsumption::FieldWrite,
        CheckedConsumption::FieldRead,
    ];
    for site in expected {
        assert!(
            reached.contains(&site),
            "no sampled instruction reaches {site:?}; the dispatch arm for it is \
             unreachable and its coverage claim is a fiction"
        );
    }
    assert_eq!(
        reached.len(),
        expected.len(),
        "the sample reached {reached:?}, expected exactly {expected:?}"
    );
}

#[test]
fn the_previously_uncovered_sites_are_now_classified_as_checked() {
    // The three holes WP-1B was opened to close, pinned by name so a future
    // reclassification of any of them is a test failure and not a quiet
    // regression.
    let store = Inst::Store {
        ty: Ty::I64,
        ptr: ValueId::new(0),
        value: ValueId::new(1),
        volatile: false,
        align: None,
    };
    assert_eq!(
        consumption_role(&store),
        ConsumptionRole::Checked(CheckedConsumption::StoreValue)
    );

    let call_indirect = Inst::CallIndirect {
        callee: ValueId::new(0),
        sig: FuncTyId::new(0),
        args: vec![],
        calling_conv: trust_ir::CallingConv::C,
    };
    assert_eq!(
        consumption_role(&call_indirect),
        ConsumptionRole::Checked(CheckedConsumption::IndirectCallArgs)
    );

    let insert_field = Inst::InsertField {
        ty: Ty::I64,
        aggregate: ValueId::new(0),
        field: 0,
        value: ValueId::new(1),
    };
    assert_eq!(
        consumption_role(&insert_field),
        ConsumptionRole::Checked(CheckedConsumption::FieldWrite)
    );

    let extract_field = Inst::ExtractField {
        ty: Ty::I64,
        aggregate: ValueId::new(0),
        field: 0,
    };
    assert_eq!(
        consumption_role(&extract_field),
        ConsumptionRole::Checked(CheckedConsumption::FieldRead)
    );

    // And `Invoke` covers BOTH halves — its arguments AND its normal edge.
    // Checking only the call half was itself a hole.
    let invoke = Inst::Invoke {
        callee: FuncId::new(0),
        args: vec![],
        normal_dest: BlockId::new(1),
        normal_args: vec![],
        unwind_dest: BlockId::new(2),
    };
    assert_eq!(
        consumption_role(&invoke),
        ConsumptionRole::Checked(CheckedConsumption::InvokeArgsAndNormalEdge)
    );
}

/// One instance of every `Inst` variant. Deliberately hand-written: the point
/// is that a NEW variant breaks `consumption_role`'s exhaustive match at
/// compile time, and this list is what proves the classification is exercised
/// rather than merely written.
fn sample_of_every_instruction() -> Vec<Inst> {
    use trust_ir::inst::{
        AllocOrigin, AtomicRMWOp, BindingFrameDef, BindingSlot, CastOp, FCmpOp, ICmpOp, Ordering,
        OverflowOp, SwitchCase, UnOp,
    };
    let v = ValueId::new;
    let b = BlockId::new;
    vec![
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::UnOp {
            op: UnOp::Neg,
            ty: Ty::I64,
            operand: v(0),
        },
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::F64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I8,
            dst_ty: Ty::I64,
            operand: v(0),
        },
        Inst::Load {
            ty: Ty::I64,
            ptr: v(0),
            volatile: false,
            align: None,
        },
        Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        },
        Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        },
        Inst::HeapAlloc {
            ty: Ty::I64,
            count: None,
            align: None,
            origin: AllocOrigin::CMalloc,
        },
        Inst::GEP {
            pointee_ty: Ty::I64,
            base: v(0),
            indices: vec![v(1)],
            inbounds: false,
        },
        Inst::PtrData {
            ptr_ty: Ty::Ptr,
            ptr: v(0),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Unit,
            ptr: v(0),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Unit,
            data: v(0),
            metadata: v(1),
        },
        Inst::AtomicLoad {
            ty: Ty::I64,
            ptr: v(0),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicStore {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicRMW {
            op: AtomicRMWOp::Xchg,
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::CmpXchg {
            ty: Ty::I64,
            ptr: v(0),
            expected: v(1),
            desired: v(2),
            success: Ordering::SeqCst,
            failure: Ordering::SeqCst,
        },
        Inst::Fence {
            ordering: Ordering::SeqCst,
        },
        Inst::Br {
            target: b(1),
            args: vec![],
        },
        Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        },
        Inst::Switch {
            value: v(0),
            default: b(1),
            default_args: vec![],
            cases: Vec::<SwitchCase>::new(),
            exhaustive_enum_unreachable: false,
        },
        Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::CallIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: trust_ir::CallingConv::C,
        },
        Inst::Return { values: vec![] },
        Inst::ExtractField {
            ty: Ty::I64,
            aggregate: v(0),
            field: 0,
        },
        Inst::InsertField {
            ty: Ty::I64,
            aggregate: v(0),
            field: 0,
            value: v(1),
        },
        Inst::ExtractElement {
            ty: Ty::I64,
            array: v(0),
            index: v(1),
        },
        Inst::InsertElement {
            ty: Ty::I64,
            array: v(0),
            index: v(1),
            value: v(2),
        },
        Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(0),
        },
        Inst::NullPtr,
        Inst::GlobalAddr {
            global: trust_ir::value::GlobalId::new(0),
        },
        Inst::Undef { ty: Ty::I64 },
        Inst::Assume { cond: v(0) },
        Inst::Assert { cond: v(0) },
        Inst::Unreachable,
        Inst::Copy {
            ty: Ty::I64,
            operand: v(0),
        },
        Inst::Select {
            ty: Ty::I64,
            cond: v(0),
            then_val: v(1),
            else_val: v(2),
        },
        Inst::SeqMapAddK {
            ty: Ty::I64,
            seq: v(0),
            k: 1,
        },
        Inst::SeqMapNot {
            ty: Ty::I64,
            seq: v(0),
        },
        Inst::SeqMap {
            ty: Ty::I64,
            seq: v(0),
            fwd: FuncId::new(0),
        },
        Inst::Borrow { ptr: v(0) },
        Inst::BorrowMut { ptr: v(0) },
        Inst::EndBorrow { borrow_ptr: v(0) },
        Inst::Retain { ptr: v(0) },
        Inst::Release { ptr: v(0) },
        Inst::IsUnique { ptr: v(0) },
        Inst::Dealloc { ptr: v(0) },
        Inst::OpenFrame {
            def: BindingFrameDef::new(
                trust_ir::value::BindingFrameId::new(0),
                "frame",
                vec![BindingSlot::new("s", Ty::I64)],
            ),
        },
        Inst::BindSlot {
            frame: v(0),
            slot: 0,
            value: v(1),
        },
        Inst::LoadSlot {
            frame: v(0),
            slot: 0,
            ty: Ty::I64,
        },
        Inst::CloseFrame { frame: v(0) },
        Inst::CoroSuspend {
            frame: v(0),
            state_slot: 0,
            next_state: 1,
            value: v(1),
        },
        Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![],
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
        Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        },
        Inst::Resume { exn: v(0) },
        Inst::DialectOp(Box::new(trust_ir::dialect::DialectInst::new(
            "verif", "probe",
        ))),
    ]
}

// ---------------------------------------------------------------------------
// WP-1B/G2 — propagation, observed through the validator
// ---------------------------------------------------------------------------
//
// The rule set and its per-rule (a)-derives / (b)-falls-to-Top pairs live as
// unit tests in `trust_ir::propagate`. What this section proves is the thing
// only the validator can show: that a DERIVED fact reaches a consumption site
// and changes the answer there, in both directions.
//
// SCOPE NOTE, stated rather than hidden: most instructions require their
// operands to have EXACTLY the instruction's declared type (`check_binop_
// operands`, `check_operand_matches_declared`), so a `Copy`/`Select`/`BinOp`
// cannot today carry an operand whose refinement differs from its own declared
// one. Propagation is therefore observable through the validator exactly where
// a result's type is NOT restated by the instruction — a comparison's boolean
// result, a block parameter's join — and wherever the derived fact is strictly
// sharper than the declared one. Relaxing those operand rules to
// REPRESENTATION equality (which is what `Ty::Refine` promises) would widen
// that surface; it is deliberately out of WP-1B's scope, because it changes a
// rule the consumption gate does not yet cover.

/// ```text
/// fn sink(b: refine<bool, required>)
/// fn f(x: i64, y: i64) { %c = icmp slt %x, %y; call @sink(%c); ret }
/// ```
///
/// A comparison's result type is not restated by the instruction, so the value
/// arrives at the call declaring NOTHING. Only propagation can say anything
/// about it — and what it says is justified by the result type alone: a
/// boolean carrier is 0 or 1.
fn cmp_fixture(required: Pred) -> Module {
    let mut module = Module::new("cmp_prop");
    let bool_ty = module.add_type(Ty::Bool);
    let required = module.intern_pred(required).expect("canonical");
    let sink_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Refine(bool_ty, required)],
        returns: vec![],
        is_vararg: false,
    });
    let f_ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![],
        is_vararg: false,
    });

    let mut sink = Function::new(FuncId::new(0), "sink", sink_ty, BlockId::new(0));
    let mut sb = Block::new(BlockId::new(0));
    sb.params
        .push((ValueId::new(0), Ty::Refine(bool_ty, required)));
    sb.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    sink.blocks.push(sb);
    module.functions.push(sink);

    let mut f = Function::new(FuncId::new(1), "f", f_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::I64));
    b.params.push((ValueId::new(1), Ty::I64));
    b.body.push(
        InstrNode::new(Inst::ICmp {
            op: trust_ir::inst::ICmpOp::Slt,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_results(vec![ValueId::new(2)]),
    );
    b.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(2)],
    }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

#[test]
fn a_derived_fact_satisfies_a_site_the_declaration_alone_cannot() {
    // (a) DERIVED WHEN JUSTIFIED. The comparison result declares nothing, so
    // under WP-1 it reached the call as `top` and was refused. Propagation
    // derives `[0, 1]` from the boolean carrier and the site is satisfied.
    assert_clean(
        &cmp_fixture(Pred::Interval { lo: 0, hi: 1 }),
        "a comparison result satisfies an in[0,1] site through propagation",
    );

    // (b) AND IT DOES NOT OVERREACH. One axis moved — what the site demands.
    // `[0, 1]` does not imply `[1, 1]`, and propagation must not pretend
    // otherwise just because it produced a fact.
    let m = cmp_fixture(Pred::Interval { lo: 1, hi: 1 });
    let errors = validate_module(&m);
    assert_eq!(errors.len(), 1, "{}", render(&errors));
    let ValidationError::RefinementNotImplied {
        actual, required, ..
    } = &errors[0]
    else {
        panic!("expected RefinementNotImplied, got {:?}", errors[0]);
    };
    assert!(
        actual.contains("propagation derives only in[0, 1]"),
        "the DERIVED fact must be named too, so the diagnostic says what the \
         computation actually guarantees: {actual}"
    );
    assert!(required.contains("in[1, 1]"), "{required}");
}

/// ```text
/// fn sink(s: refine<T, [200, 254]>)
/// fn f(a: refine<T, [100, 127]>, b: refine<T, [100, 127]>) {
///   %s = add <T> a, b ; call @sink(%s); ret
/// }
/// ```
///
/// `T` is the ONLY axis: `i8` cannot hold 200, `i16` can.
fn overflow_fixture(base: Ty) -> Module {
    let mut module = Module::new("overflow_prop");
    let base_id = module.add_type(base.clone());
    let operand = module
        .intern_pred(Pred::Interval { lo: 100, hi: 127 })
        .expect("canonical");
    let sum = module
        .intern_pred(Pred::Interval { lo: 200, hi: 254 })
        .expect("canonical");
    let operand_ty = Ty::Refine(base_id, operand);

    let sink_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Refine(base_id, sum)],
        returns: vec![],
        is_vararg: false,
    });
    let f_ty = module.add_func_type(FuncTy {
        params: vec![operand_ty.clone(), operand_ty.clone()],
        returns: vec![],
        is_vararg: false,
    });

    let mut sink = Function::new(FuncId::new(0), "sink", sink_ty, BlockId::new(0));
    let mut sb = Block::new(BlockId::new(0));
    sb.params.push((ValueId::new(0), Ty::Refine(base_id, sum)));
    sb.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    sink.blocks.push(sb);
    module.functions.push(sink);

    let mut f = Function::new(FuncId::new(1), "f", f_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), operand_ty.clone()));
    b.params.push((ValueId::new(1), operand_ty.clone()));
    b.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            // The result declares no fact. The call below must therefore be
            // justified by propagation alone: `i16` derives [200,254], while
            // `i8` drops to Top at the wrap gate.
            ty: base,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_results(vec![ValueId::new(2)]),
    );
    b.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(2)],
    }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

#[test]
fn propagation_falls_to_top_when_the_arithmetic_could_wrap() {
    // (b) THE OVERFLOW GATE at validator level. In an `i8` carrier
    // `[100,127] + [100,127]` runs past 127, the machine wraps, and the
    // interval would be a LIE — so the fact is dropped and the site fails.
    let m = overflow_fixture(Ty::I8);
    let errors = validate_module(&m);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::RefinementNotImplied { .. })),
        "an overflowing add must derive nothing, got: {}",
        render(&errors)
    );

    // (a) ONE AXIS MOVED — the carrier width. The identical arithmetic in an
    // `i16` cannot wrap, so the interval survives and satisfies the site. This
    // is what proves the refusal above is the overflow gate and not a blanket
    // refusal to do arithmetic.
    assert_clean(
        &overflow_fixture(Ty::I16),
        "the same add in a carrier wide enough not to wrap",
    );
}

/// ```text
/// fn f(a: refine<i16, p>, b: refine<i16, p>) { %s = add <refine<i16,p>> a, b; ret }
/// ```
///
/// The producer declares the SUM still satisfies `p`. For `p = [100, 127]`
/// that is false and decidably so.
fn contradiction_fixture(p: Pred) -> Module {
    let mut module = Module::new("contradiction");
    let base_id = module.add_type(Ty::I16);
    let p = module.intern_pred(p).expect("canonical");
    let ty = Ty::Refine(base_id, p);
    let f_ty = module.add_func_type(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "f", f_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), ty.clone()));
    b.params.push((ValueId::new(1), ty.clone()));
    b.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_results(vec![ValueId::new(2)]),
    );
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    module.functions.push(f);
    module
}

#[test]
fn a_declaration_that_propagation_contradicts_is_a_hard_error() {
    // THE INTERSECTION RULE, MADE LOUD.
    //
    // Declared and derived are two claims about ONE value, so the value
    // satisfies both. When their intersection is decidably EMPTY, that is not
    // an imprecision to widen away: the producer declared something the
    // program does not produce, which is a frontend bug of exactly the class
    // this model exists to surface. Widening it to `top` would hide it.
    let m = contradiction_fixture(Pred::Interval { lo: 100, hi: 127 });
    let errors = validate_module(&m);
    assert_eq!(
        errors.len(),
        1,
        "expected exactly the contradiction, got: {}",
        render(&errors)
    );
    let ValidationError::RefinementContradicted {
        location,
        declared,
        derived,
    } = &errors[0]
    else {
        panic!("expected RefinementContradicted, got {:?}", errors[0]);
    };
    assert!(location.contains("%2"), "{location}");
    assert!(declared.contains("in[100, 127]"), "{declared}");
    assert!(
        derived.contains("in[200, 254]"),
        "the derived fact must be NAMED, so the diagnostic says what the \
         computation actually produces: {derived}"
    );

    // ── PERTURBATION: one axis — the declared interval's lower bound ──────
    // `[0,127] + [0,127] = [0,254]`, which OVERLAPS `[0,127]`. Same
    // instruction, same carrier width, same propagation, same tables — the
    // declaration is merely no longer refuted, and the module is clean.
    assert_clean(
        &contradiction_fixture(Pred::Interval { lo: 0, hi: 127 }),
        "PERTURBATION: a declaration the arithmetic does not refute",
    );
}

#[test]
fn a_block_parameter_takes_the_join_of_its_predecessors() {
    // WP-1 checks each EDGE against the join site's declared type. G2 adds the
    // other half: the parameter's own derived fact is the JOIN over those
    // edges, so a merge of two facts can satisfy a later site even when the
    // parameter itself declares nothing.
    //
    // ```text
    // fn f(c: bool, x: refine<i64,[0,3]>, y: refine<i64,[7,9]>) {
    //   bb0: condbr c -> bb1(x) / bb1(y)
    //   bb1(k: i64):  call @sink(k)   ; @sink wants refine<i64,[0,9]>
    // }
    // ```
    fn build(seed: Seed, sink_pred: PredId, a: PredId, b: PredId) -> Module {
        let Seed {
            mut module, i64_ty, ..
        } = seed;
        let sink_ty = module.add_func_type(FuncTy {
            params: vec![Ty::Refine(i64_ty, sink_pred)],
            returns: vec![],
            is_vararg: false,
        });
        let f_ty = module.add_func_type(FuncTy {
            params: vec![Ty::Bool, Ty::Refine(i64_ty, a), Ty::Refine(i64_ty, b)],
            returns: vec![],
            is_vararg: false,
        });

        let mut sink = Function::new(FuncId::new(0), "sink", sink_ty, BlockId::new(0));
        let mut sb = Block::new(BlockId::new(0));
        sb.params
            .push((ValueId::new(0), Ty::Refine(i64_ty, sink_pred)));
        sb.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        sink.blocks.push(sb);
        module.functions.push(sink);

        let mut f = Function::new(FuncId::new(1), "f", f_ty, BlockId::new(0));
        let mut bb0 = Block::new(BlockId::new(0));
        bb0.params.push((ValueId::new(0), Ty::Bool));
        bb0.params.push((ValueId::new(1), Ty::Refine(i64_ty, a)));
        bb0.params.push((ValueId::new(2), Ty::Refine(i64_ty, b)));
        bb0.body.push(InstrNode::new(Inst::CondBr {
            cond: ValueId::new(0),
            then_target: BlockId::new(1),
            then_args: vec![ValueId::new(1)],
            else_target: BlockId::new(1),
            else_args: vec![ValueId::new(2)],
        }));
        f.blocks.push(bb0);
        let mut bb1 = Block::new(BlockId::new(1));
        // The join site declares NOTHING: only the derived join can satisfy
        // the call below.
        bb1.params.push((ValueId::new(3), Ty::I64));
        bb1.body.push(InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(3)],
        }));
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(bb1);
        module.functions.push(f);
        module
    }

    // (a) the hull of [0,3] and [7,9] is [0,9], which satisfies the site.
    let mut s = seed("join_ok");
    let a = s
        .module
        .intern_pred(Pred::Interval { lo: 0, hi: 3 })
        .expect("canonical");
    let b = s
        .module
        .intern_pred(Pred::Interval { lo: 7, hi: 9 })
        .expect("canonical");
    let need = s
        .module
        .intern_pred(Pred::Interval { lo: 0, hi: 9 })
        .expect("canonical");
    assert_clean(
        &build(s, need, a, b),
        "the join [0,9] satisfies an [0,9] site",
    );

    // (b) one axis moved: the site now needs [0, 5], which the join does NOT
    // provide. The merge must lose, loudly.
    let mut s = seed("join_fail");
    let a = s
        .module
        .intern_pred(Pred::Interval { lo: 0, hi: 3 })
        .expect("canonical");
    let b = s
        .module
        .intern_pred(Pred::Interval { lo: 7, hi: 9 })
        .expect("canonical");
    let need = s
        .module
        .intern_pred(Pred::Interval { lo: 0, hi: 5 })
        .expect("canonical");
    let m = build(s, need, a, b);
    let errors = validate_module(&m);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::RefinementNotImplied { .. })),
        "the join must not satisfy a site stronger than the hull: {}",
        render(&errors)
    );
}

#[test]
fn a_loop_carried_value_derives_nothing_rather_than_a_fixpoint_guess() {
    // Propagation is a SINGLE reverse-postorder pass: a back edge contributes
    // `top`, so a loop-carried value simply has no derived fact. That is the
    // correct answer to "I cannot justify better", and it is why there is no
    // widening operator to argue about.
    //
    // ```text
    // fn f(x: refine<i64,[0,3]>) {
    //   bb0: br bb1(x)
    //   bb1(k: i64): br bb1(k)          ; the back edge
    // }
    // ```
    let mut s = seed("loop");
    let a = s
        .module
        .intern_pred(Pred::Interval { lo: 0, hi: 3 })
        .expect("canonical");
    let Seed {
        mut module, i64_ty, ..
    } = s;
    let f_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Refine(i64_ty, a)],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "f", f_ty, BlockId::new(0));
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((ValueId::new(0), Ty::Refine(i64_ty, a)));
    bb0.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(0)],
    }));
    f.blocks.push(bb0);
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((ValueId::new(1), Ty::I64));
    bb1.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(1)],
    }));
    f.blocks.push(bb1);
    module.functions.push(f);

    // The module is well-formed and validation TERMINATES — which is the
    // property under test. Nothing is derived across the back edge, so no
    // spurious fact and no spurious error.
    assert_clean(&module, "a loop must terminate and derive nothing");
}
