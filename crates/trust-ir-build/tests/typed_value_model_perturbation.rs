// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// PERTURBATION MATRIX for the typed value model — the anti-vacuity control.
// ══════════════════════════════════════════════════════════════════════════
//
// The vacuity trap: a fixture that fails for ANY reason is worthless. For each
// historical defect this file (a) reproduces the defect and pins that the
// failure is the CONSUMPTION RULE at the right site, and (b) perturbs the SAME
// module along exactly one axis — the axis that carries the defect — leaving
// the refinement machinery fully live, and asserts the perturbed module then
// validates with ZERO errors from the whole validator.
//
// These perturbations are chosen independently of the ones WP-1 shipped. In
// particular P1 and P3 perturb the CONSUMPTION SITE rather than the carrier,
// which the shipped controls do not do.

use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Module, Pred, PredId, Space, Ty, Universe,
    ValueId,
};
use trust_ir_build::{ValidationError, validate_module};

const M: i128 = 8;

fn report(module: &Module, what: &str) -> Vec<ValidationError> {
    let errors = validate_module(module);
    eprintln!(
        "[{what}] {} error(s): {}",
        errors.len(),
        errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join(" | ")
    );
    errors
}

fn assert_clean(module: &Module, what: &str) {
    let errors = report(module, what);
    assert!(errors.is_empty(), "{what} must validate clean");
}

fn assert_one_consumption_failure(module: &Module, what: &str, site: &str) {
    let errors = report(module, what);
    assert_eq!(errors.len(), 1, "{what}: expected exactly one error");
    match &errors[0] {
        ValidationError::RefinementNotImplied { location, .. } => {
            assert!(
                location.contains(site),
                "{what}: expected site {site:?}, got {location:?}"
            );
        }
        other => panic!("{what}: expected RefinementNotImplied, got {other:?}"),
    }
}

/// `fn key_of(x: required_ty)` + `fn row_lookup(k: carrier_ty) { call @key_of(k) }`
fn call_pair(m: &mut Module, carrier_ty: Ty, required_ty: Ty) {
    let key_of_ty = m.add_func_type(FuncTy {
        params: vec![required_ty.clone()],
        returns: vec![],
        is_vararg: false,
    });
    let row_ty = m.add_func_type(FuncTy {
        params: vec![carrier_ty.clone()],
        returns: vec![],
        is_vararg: false,
    });

    let mut key_of = Function::new(FuncId::new(0), "key_of", key_of_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), required_ty));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    key_of.blocks.push(b);
    m.functions.push(key_of);

    let mut row = Function::new(FuncId::new(1), "row_lookup", row_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), carrier_ty));
    b.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(0)],
    }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    row.blocks.push(b);
    m.functions.push(row);
}

// ── WP-18 ────────────────────────────────────────────────────────────────────

/// carrier_space=None means the carrier is a raw `Interval{0, M}` (the shipped
/// off-by-one); Some(s) means `InUniverse(U, s)`. required_space is the
/// convention the consumption site demands.
fn wp18(carrier_space: Option<Space>, required_space: Option<Space>) -> Module {
    let mut m = Module::new("wp18_perturbable");
    let i64_ty = m.add_type(Ty::I64);
    let u = m
        .intern_universe(Universe::IntRange { lo: 1, hi: M })
        .expect("canonical");

    let required = match required_space {
        Some(s) => m.intern_pred(Pred::InUniverse(u, s)).expect("in range"),
        // Perturbation P1: the site asks only for the RAW NUMERIC fact.
        None => m
            .intern_pred(Pred::Interval { lo: 0, hi: M })
            .expect("canonical"),
    };
    let carrier = match carrier_space {
        Some(s) => m.intern_pred(Pred::InUniverse(u, s)).expect("in range"),
        None => m
            .intern_pred(Pred::Interval { lo: 0, hi: M })
            .expect("canonical"),
    };

    call_pair(
        &mut m,
        Ty::Refine(i64_ty, carrier),
        Ty::Refine(i64_ty, required),
    );
    m
}

#[test]
fn wp18_defect_then_perturbations() {
    // ── THE DEFECT ────────────────────────────────────────────────────────
    // A raw index interval reaching a MEMBER site.
    assert_one_consumption_failure(
        &wp18(None, Some(Space::Member)),
        "DEFECT: raw index interval -> member site",
        "call @key_of arg 0",
    );
    // The sharper form: same universe, same machine word, only the convention
    // differs. This is the statement that did not exist at HEAD.
    assert_one_consumption_failure(
        &wp18(Some(Space::Index), Some(Space::Member)),
        "DEFECT: index-into-U -> member-of-U site",
        "call @key_of arg 0",
    );

    // ── PERTURBATION P1: weaken the SITE, keep the carrier ────────────────
    // Exactly one axis moved (what the site requires). The carrier, the
    // universe, the refinement machinery and the call are all unchanged.
    assert_clean(
        &wp18(None, None),
        "P1: raw index interval -> raw-interval site",
    );

    // ── PERTURBATION P3: flip the SITE's convention to match the carrier ──
    // The universe, representation and value are IDENTICAL to the defect
    // above; only the demanded convention changed. If the fixture failed for
    // any reason other than the convention, this would still fail.
    assert_clean(
        &wp18(Some(Space::Index), Some(Space::Index)),
        "P3: index-into-U -> index-into-U site",
    );

    // ── PERTURBATION P2: fix the CARRIER, keep the site ───────────────────
    assert_clean(
        &wp18(Some(Space::Member), Some(Space::Member)),
        "P2: member-of-U -> member-of-U site",
    );

    // And the converse direction is refused too, which rules out the check
    // being a one-sided space test that happens to fire.
    assert_one_consumption_failure(
        &wp18(Some(Space::Member), Some(Space::Index)),
        "DEFECT (converse): member-of-U -> index-into-U site",
        "call @key_of arg 0",
    );
}

// ── WP-28 ────────────────────────────────────────────────────────────────────

/// `bb0(c,x,y): condbr c -> bb1(x)/bb1(y)`, `bb1(k: join_ty)`.
fn wp28(edge_a: Ty, edge_b: Ty, join_ty: Ty) -> Module {
    let mut m = Module::new("wp28_perturbable");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::Bool, edge_a.clone(), edge_b.clone()],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "merge", ft, BlockId::new(0));
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((ValueId::new(0), Ty::Bool));
    bb0.params.push((ValueId::new(1), edge_a));
    bb0.params.push((ValueId::new(2), edge_b));
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(0),
        then_target: BlockId::new(1),
        then_args: vec![ValueId::new(1)],
        else_target: BlockId::new(1),
        else_args: vec![ValueId::new(2)],
    }));
    f.blocks.push(bb0);
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((ValueId::new(3), join_ty));
    bb1.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(bb1);
    m.functions.push(f);
    m
}

#[test]
fn wp28_defect_then_perturbations() {
    // ── THE DEFECT: one edge dropped the fact ─────────────────────────────
    {
        let mut m = Module::new("seed");
        let i64_ty = m.add_type(Ty::I64);
        let p = m
            .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
            .expect("canonical");
        let (u, preds) = (m.universes.clone(), m.predicates.clone());
        let mut d = wp28(Ty::Refine(i64_ty, p), Ty::I64, Ty::Refine(i64_ty, p));
        d.types = vec![Ty::I64];
        d.universes = u.clone();
        d.predicates = preds.clone();
        assert_one_consumption_failure(
            &d,
            "DEFECT: one edge dropped the fact",
            "bb0 -> bb1 join arg 0",
        );

        // ── PERTURBATION P5: the join site requires nothing ───────────────
        // The refined edge is still there and the table is still live; only
        // the site's requirement moved. Absence must be permitted where
        // nothing is demanded.
        let mut p5 = wp28(Ty::Refine(i64_ty, p), Ty::I64, Ty::I64);
        p5.types = vec![Ty::I64];
        p5.universes = u.clone();
        p5.predicates = preds.clone();
        assert_clean(&p5, "P5: join site requires nothing");
    }

    // ── DEFECT: two genuinely different universes ─────────────────────────
    {
        let mut m = Module::new("seed2");
        let i64_ty = m.add_type(Ty::I64);
        let a = m
            .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
            .expect("canonical");
        let b = m
            .intern_in_universe(Universe::IntRange { lo: 100, hi: 200 }, Space::Member)
            .expect("canonical");
        let table = m.pred_table();
        assert!(!table.implies(b, a));
        let (u, preds) = (m.universes.clone(), m.predicates.clone());

        let mut d = wp28(
            Ty::Refine(i64_ty, a),
            Ty::Refine(i64_ty, b),
            Ty::Refine(i64_ty, a),
        );
        d.types = vec![Ty::I64];
        d.universes = u;
        d.predicates = preds;
        assert_one_consumption_failure(
            &d,
            "DEFECT: incomparable universes at the join",
            "bb0 -> bb1 join arg 0",
        );
    }

    // ── PERTURBATION P4: make edge B's universe a SUBSET of the site's ────
    // One axis moved: 100..=200 becomes 2..=5. Two distinct universes, two
    // distinct PredIds, both edges still refined — but the entailment now
    // holds, so the join survives. This proves the failure above came from
    // the entailment, not from "two ids at a join".
    {
        let mut m = Module::new("seed3");
        let i64_ty = m.add_type(Ty::I64);
        let a = m
            .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
            .expect("canonical");
        let b = m
            .intern_in_universe(Universe::IntRange { lo: 2, hi: 5 }, Space::Member)
            .expect("canonical");
        assert_ne!(a, b, "P4 must still involve two distinct predicate ids");
        let (u, preds) = (m.universes.clone(), m.predicates.clone());

        let mut p4 = wp28(
            Ty::Refine(i64_ty, a),
            Ty::Refine(i64_ty, b),
            Ty::Refine(i64_ty, a),
        );
        p4.types = vec![Ty::I64];
        p4.universes = u;
        p4.predicates = preds;
        assert_clean(&p4, "P4: edge B over a sub-universe of the join site");
    }

    // ── PERTURBATION P6: same universe, two independent mints ─────────────
    // The structural fix, restated: content-interning collapses them to ONE
    // id, so the join preserves the fact.
    {
        let mut m = Module::new("seed4");
        let i64_ty = m.add_type(Ty::I64);
        let a = m
            .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
            .expect("canonical");
        let b = m
            .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
            .expect("canonical");
        assert_eq!(a, b, "content interning must collapse two mints to one id");
        assert_eq!(m.universes.len(), 1);
        assert_eq!(m.predicates.len(), 1);
        let (u, preds) = (m.universes.clone(), m.predicates.clone());
        let mut p6 = wp28(
            Ty::Refine(i64_ty, a),
            Ty::Refine(i64_ty, b),
            Ty::Refine(i64_ty, a),
        );
        p6.types = vec![Ty::I64];
        p6.universes = u;
        p6.predicates = preds;
        assert_clean(&p6, "P6: same universe minted twice");
    }
}

#[test]
fn the_defect_is_invisible_without_refinements() {
    // The baseline both defects reduce to when the convention is not statable:
    // identical control flow and identical machine types, zero errors. This is
    // why the miscompiles shipped.
    let m = wp28(Ty::I64, Ty::I64, Ty::I64);
    assert_clean(&m, "BASELINE: the same join with no refinements");

    let mut m = Module::new("wp18_baseline");
    call_pair(&mut m, Ty::I64, Ty::I64);
    assert_clean(&m, "BASELINE: the same call with no refinements");
}

#[test]
fn no_raw_numeric_shape_promotes_into_a_membership_convention() {
    // A NUMERIC fact never becomes a CONVENTION, even when the numbers agree
    // exactly. This is the load-bearing asymmetry of the whole design: the
    // convention is not derivable from the value, so it can only come from
    // another convention-carrying fact.
    //
    // The cost is a precision loss (a producer that knows `self ∈ {2,3,4}`
    // must SAY `in_universe({2,3,4}, member)`, not `in{2,3,4}`, to satisfy a
    // membership site). The cost is paid in the loud direction: a spurious
    // error, never a spurious acceptance.
    let mut m = Module::new("no_promotion");
    let u = m
        .intern_universe(Universe::IntRange { lo: 1, hi: M })
        .expect("canonical");
    let required = m
        .intern_pred(Pred::InUniverse(u, Space::Member))
        .expect("in range");
    // A finite set entirely INSIDE the universe.
    let subset_set = m
        .intern_pred(Pred::FiniteSet(
            [2i128, 3, 4].into_iter().map(Constant::Int).collect(),
        ))
        .expect("canonical");
    // An interval NUMERICALLY IDENTICAL to the universe.
    let exact_interval = m
        .intern_pred(Pred::Interval { lo: 1, hi: M })
        .expect("canonical");
    let table = m.pred_table();
    assert!(
        !table.implies(subset_set, required),
        "a finite set of members must NOT promote into a membership convention"
    );
    assert!(
        !table.implies(exact_interval, required),
        "nor an interval that numerically equals the universe"
    );
    // The reverse direction — a convention DOES entail its numeric content —
    // is sound and does hold, which is what makes this a directional lattice
    // rather than a wall.
    assert!(table.implies(required, exact_interval));
    assert!(
        !table.implies(required, subset_set),
        "but only where the numbers actually contain it"
    );

    // The consequence at a real consumption site.
    let i64_ty = m.add_type(Ty::I64);
    call_pair(
        &mut m,
        Ty::Refine(i64_ty, subset_set),
        Ty::Refine(i64_ty, required),
    );
    assert_one_consumption_failure(
        &m,
        "finite set {2,3,4} -> member of 1..=8 (refused BY DESIGN)",
        "call @key_of arg 0",
    );

    // The sanctioned way to say the same thing IS accepted — so the rule is a
    // spelling requirement, not an expressiveness dead end.
    let mut m2 = Module::new("no_promotion_sanctioned");
    let i64_ty = m2.add_type(Ty::I64);
    let u = m2
        .intern_universe(Universe::IntRange { lo: 1, hi: M })
        .expect("canonical");
    let required = m2
        .intern_pred(Pred::InUniverse(u, Space::Member))
        .expect("in range");
    let carrier = m2
        .intern_in_universe(
            Universe::Members([2i128, 3, 4].into_iter().map(Constant::Int).collect()),
            Space::Member,
        )
        .expect("canonical");
    assert_ne!(carrier, required);
    call_pair(
        &mut m2,
        Ty::Refine(i64_ty, carrier),
        Ty::Refine(i64_ty, required),
    );
    assert_clean(&m2, "in_universe({2,3,4}, member) -> member of 1..=8");
    let _ = PredId::new(0);
}
