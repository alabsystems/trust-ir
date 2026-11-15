// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `trust_ir_contract::Formula::ConstArray` solved by ay. The contract crate
// owns the SMT-LIB text a `Formula` lowers to, so these tests hand ay exactly
// what `Formula::to_smtlib` emits and check what it MEANS:
//
//   * a read of a constant array is its value, at every index, including
//     indices far past any Rust array length;
//   * a store over a constant array overrides exactly one index;
//   * `[v; N]` stated as `arr = ConstArray(v)` is the same term for every N,
//     and the read at lane N - 1 is proved for N up to 2^63;
//   * ay's in-process `Solver::const_array(index_sort, value)` gives the same
//     verdicts as the text, so a bridge that lowers the node by its two
//     fields keeps the node's meaning.
//
// Every "valid" claim is paired with a satisfiable neighbour, so a solver
// that answered UNSAT to everything would fail here.

#![allow(clippy::disallowed_methods)] // a test drives ay directly; a panic here is a test failure (r11 item 5, crates/trust-ir-ay/clippy.toml)

use ay::{Logic, Solver, VerifiedSolveResult};
use trust_ir_contract::{Formula, Sort};

fn solver() -> Solver {
    Solver::try_new(Logic::All).expect("ay solver for arrays + bitvectors + ints")
}

/// Declare `decls`, assert every formula as `Formula::to_smtlib` spells it,
/// and check satisfiability.
fn check(decls: &str, assertions: &[Formula]) -> VerifiedSolveResult {
    let mut script = decls.to_string();
    for f in assertions {
        script.push_str(&format!("(assert {})\n", f.to_smtlib()));
    }
    let mut s = solver();
    s.parse_smtlib2(&script)
        .unwrap_or_else(|e| panic!("ay refused the emitted SMT-LIB:\n{script}\n{e}"));
    s.check_sat()
}

/// `goal` holds in every model of `decls`: its negation is UNSAT.
fn valid(decls: &str, goal: Formula) -> bool {
    check(decls, &[Formula::Not(Box::new(goal))]).is_unsat()
}

fn satisfiable(decls: &str, assertions: &[Formula]) -> bool {
    check(decls, assertions).is_sat()
}

fn int(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

fn bv(name: &str, width: u32) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(width))
}

fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}

fn select(arr: Formula, idx: Formula) -> Formula {
    Formula::Select(Box::new(arr), Box::new(idx))
}

fn store(arr: Formula, idx: Formula, val: Formula) -> Formula {
    Formula::Store(Box::new(arr), Box::new(idx), Box::new(val))
}

fn u64_bv(n: u64) -> Formula {
    Formula::BitVec {
        value: i128::from(n),
        width: 64,
    }
}

#[test]
fn a_read_of_a_const_array_is_its_value() {
    let decls = "(declare-const k Int)\n(declare-const v Int)\n";
    let base = Formula::const_array(Sort::Int, Sort::Int, int("v"));
    assert!(
        valid(decls, eq(select(base.clone(), int("k")), int("v"))),
        "select(const(v), k) = v for every k"
    );
    // Non-vacuity: the read is not forced to anything else.
    assert!(satisfiable(
        decls,
        &[eq(select(base, int("k")), Formula::Int(5))]
    ));

    // The bitvector lane: a usize-indexed byte array, read at an index that
    // is past any real allocation.
    let decls = "(declare-const b (_ BitVec 8))\n";
    let bytes = Formula::const_array(Sort::BitVec(64), Sort::BitVec(8), bv("b", 8));
    assert!(valid(
        decls,
        eq(select(bytes, u64_bv(u64::MAX)), bv("b", 8))
    ));
}

#[test]
fn a_store_over_a_const_array_overrides_exactly_one_index() {
    let decls = "(declare-const k Int)\n";
    let seven = Formula::const_array(Sort::Int, Sort::Int, Formula::Int(7));
    let a = store(seven, Formula::Int(3), Formula::Int(9));

    assert!(valid(
        decls,
        eq(select(a.clone(), Formula::Int(3)), Formula::Int(9))
    ));
    let elsewhere = Formula::Implies(
        Box::new(Formula::Not(Box::new(eq(int("k"), Formula::Int(3))))),
        Box::new(eq(select(a.clone(), int("k")), Formula::Int(7))),
    );
    assert!(valid(decls, elsewhere));

    // The only two values the array holds are both reachable…
    assert!(satisfiable(
        decls,
        &[eq(select(a.clone(), int("k")), Formula::Int(9))]
    ));
    assert!(satisfiable(
        decls,
        &[eq(select(a.clone(), int("k")), Formula::Int(7))]
    ));
    // …and nothing else is.
    assert!(!satisfiable(
        decls,
        &[eq(select(a, int("k")), Formula::Int(8))]
    ));
}

/// `[v; N]` stated as `arr = ConstArray(v)` proves the read at lane `N - 1`
/// for every N, with the same statement each time. A free base array (what
/// vcgen falls back to above 64 elements today) proves nothing about it.
#[test]
fn uniform_array_seed_is_constant_size_and_exact_in_n() {
    let decls = "(declare-const arr (Array (_ BitVec 64) (_ BitVec 8)))\n\
                 (declare-const v (_ BitVec 8))\n";
    let arr = || {
        Formula::Var(
            "arr".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        )
    };
    let seed = eq(
        arr(),
        Formula::const_array(Sort::BitVec(64), Sort::BitVec(8), bv("v", 8)),
    );
    let seed_text = seed.to_smtlib();

    for n in [2_u64, 64, 65, 1 << 20, 1 << 40, 1 << 63] {
        let last = eq(select(arr(), u64_bv(n - 1)), bv("v", 8));
        assert_eq!(
            seed.to_smtlib(),
            seed_text,
            "the statement of [v; {n}] does not mention {n}"
        );
        assert!(
            valid(
                decls,
                Formula::Implies(Box::new(seed.clone()), Box::new(last.clone()))
            ),
            "[v; {n}][{n} - 1] == v"
        );
        // Without the seed (a free base) the lane is unconstrained.
        assert!(
            satisfiable(decls, &[Formula::Not(Box::new(last))]),
            "a free base proves nothing about lane {n} - 1"
        );
    }
}

/// ay's in-process API takes a constant array as `(index_sort, value)`,
/// the element sort coming from `value`. Lowering the node by its fields
/// that way gives the same verdicts as the text.
#[test]
fn in_process_const_array_agrees_with_the_text() {
    let f = Formula::const_array(Sort::BitVec(64), Sort::BitVec(8), bv("v", 8));
    let Formula::ConstArray {
        index_sort,
        elem_sort,
        value,
    } = &f
    else {
        unreachable!("const_array builds a ConstArray");
    };
    assert_eq!(*index_sort, Sort::BitVec(64));
    assert_eq!(*elem_sort, Sort::BitVec(8));
    assert_eq!(**value, bv("v", 8));

    let mut s = solver();
    let v = s.declare_const("v", ay::Sort::bitvec(8));
    let base = s.const_array(ay::Sort::bitvec(64), v);
    let far = s.bv_const_u64(u64::MAX, 64);
    let read = s.select(base, far);
    let same = s.eq(read, v);
    let differs = s.not(same);
    s.assert_term(differs);
    assert!(
        s.check_sat().is_unsat(),
        "in-process: select(const(v), i) = v"
    );

    let decls = "(declare-const v (_ BitVec 8))\n";
    assert!(valid(decls, eq(select(f, u64_bv(u64::MAX)), bv("v", 8))));
}
