// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `trust_ir_contract::formula_dag` printers checked by ay: the sharing text
// means what the tree text means.
//
//   * EQUIVALENCE: for a witness of every `Formula` variant — each used
//     TWICE, so a compound witness is let-bound and its bound spelling is
//     what ay checks — and for random well-sorted formulas with shared
//     subterms (shared across binders too, over two names that occur both
//     free and bound), ay proves the `let` text equal to the tree text —
//     `(assert (not (= TREE SHARED)))` is UNSAT — and likewise every term of
//     a `define-fun` script, under its definitions; the same for the shapes
//     where a binding is hoisted across binders;
//   * VERDICTS: asserting the tree texts and asserting the sharing texts give
//     the same decided answer (rows either side leaves `unknown` within the
//     timeout are counted, not compared, and a floor of decided rows keeps
//     the comparison from passing vacuously);
//   * NON-VACUITY: the same check refutes a sharing text that hoists a
//     binding across a binder that captures it, and one that swaps two
//     bindings; a solver that answered UNSAT to everything would fail here;
//   * SORTS: ay refuses a `define-fun` whose declared sort is `Int` and
//     whose body is `Real`, and the script printer refuses to guess a sort
//     for mixed `Int`/`Real` operands.
//
// The syntactic half (the bindings expand to the tree text byte for byte,
// and no binding is captured) is `trust-ir-contract/tests/formula_dag.rs`.

#![allow(clippy::disallowed_methods)] // a test drives ay directly; a panic here is a test failure (r11 item 5, crates/trust-ir-ay/clippy.toml)

use ay::{Logic, Solver, VerifiedSolveResult};
use std::collections::HashMap;
use std::time::Duration;
use trust_ir_contract::formula_census::{
    formula_variant_names, variant_name, witness_declarations, witnesses,
};
use trust_ir_contract::formula_dag::{DagError, FormulaDag, NodeId, Shell};
use trust_ir_contract::{Formula, RoundingMode, Sort, Symbol};

/// What ay made of one script.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Answer {
    Sat,
    Unsat,
    Unknown,
    /// ay refused the text (parse, sort or unsupported-theory error).
    Refused(String),
}

fn answer(r: &VerifiedSolveResult) -> Answer {
    if r.is_unsat() {
        Answer::Unsat
    } else if r.is_sat() {
        Answer::Sat
    } else {
        Answer::Unknown
    }
}

fn run(script: &str, timeout: Duration) -> Answer {
    let mut s = match Solver::try_new(Logic::All) {
        Ok(s) => s,
        Err(e) => return Answer::Refused(format!("solver: {e}")),
    };
    s.set_timeout(Some(timeout));
    if let Err(e) = s.parse_smtlib2(script) {
        return Answer::Refused(e.to_string());
    }
    answer(&s.check_sat())
}

/// `(not (= tree shared))` under the witness declarations (plus `extra`).
/// UNSAT means ay proved the two texts equal. Generous timeout: an
/// equivalence that holds is usually immediate.
fn differs(extra: &str, tree: &str, shared: &str) -> Answer {
    run(
        &format!(
            "{}{extra}(assert (not (= {tree} {shared})))\n",
            witness_declarations()
        ),
        Duration::from_secs(20),
    )
}

/// The verdict of asserting `terms` under the declarations and `extra`. A
/// short timeout: two texts that time out alike agree (both `Unknown`).
fn assert_all(extra: &str, terms: &[String]) -> Answer {
    let mut script = witness_declarations();
    script.push_str(extra);
    for t in terms {
        script.push_str(&format!("(assert {t})\n"));
    }
    run(&script, Duration::from_secs(2))
}

/// Variants whose SMT-LIB spelling ay at the pinned rev does not accept, so
/// no equivalence can be decided for their witnesses: the tree text and the
/// sharing text must then be refused alike. Pinned so a change in ay's
/// coverage is seen here.
const AY_REFUSES: &[&str] = &[];

/// Each witness `w` is printed as `(ite p w w)`: `w` is used twice, so a
/// compound witness (or a leaf longer than any name) is let-bound and ay
/// checks its BOUND spelling, not a text identical to the tree's.
#[test]
fn every_witness_shares_equivalently() {
    let all = witnesses();
    let mut decided: Vec<&str> = Vec::new();
    let mut refused: HashMap<&str, String> = HashMap::new();
    let mut bound = 0;
    let mut dag = FormulaDag::new();
    let p = || bx(var("p", Sort::Bool));
    for w in &all {
        let twice = Formula::Ite(p(), bx(w.clone()), bx(w.clone()));
        let id = dag.intern(&twice);
        let tree = twice.to_smtlib();
        let shared = dag.to_smtlib(id);
        let name = variant_name(w);
        if Shell::of(w).arity() > 0 {
            // Checked BEFORE ay runs: sharing must not silently stop.
            assert!(
                shared.starts_with("(let ((") && shared != tree,
                "{name}: a compound witness used twice is bound: {shared}"
            );
        }
        if shared != tree {
            bound += 1;
        }
        match differs("", &tree, &shared) {
            Answer::Unsat => decided.push(name),
            Answer::Refused(why) => {
                // Refused alike: the tree text on its own is refused too.
                let alone = differs("", &tree, &tree);
                assert!(
                    matches!(alone, Answer::Refused(_)),
                    "{name}: ay refuses the sharing text ({why}) but not the tree text \
                     ({alone:?})\n  tree   {tree}\n  shared {shared}"
                );
                refused.insert(name, why);
            }
            other => panic!(
                "{name}: tree and sharing texts are not proved equal ({other:?})\n  \
                 tree   {tree}\n  shared {shared}"
            ),
        }
    }
    eprintln!(
        "decided {} witnesses ({bound} with a bound spelling); refused: {refused:#?}",
        decided.len()
    );
    assert!(
        bound * 2 > all.len(),
        "most witnesses are compound and bound"
    );
    for name in formula_variant_names() {
        let expected_refused = AY_REFUSES.contains(name);
        let is_decided = decided.contains(name);
        assert!(
            is_decided || expected_refused,
            "{name}: no witness was decided ({:?})",
            refused.get(name)
        );
    }
}

// ── Random well-sorted formulas with sharing ─────────────────────────────────

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next() % (n as u64)).unwrap_or(0)
    }
    fn chance(&mut self, num: u64, den: u64) -> bool {
        self.next() % den < num
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum S {
    Bool,
    Int,
    Bv8,
    Arr,
}

fn bx(f: Formula) -> Box<Formula> {
    Box::new(f)
}

fn var(name: &str, sort: Sort) -> Formula {
    Formula::Var(name.into(), sort)
}

/// Random well-sorted formulas over Int, bit-vector, array and Boolean terms
/// (the theories the strict lanes use), with shared subterms drawn back from
/// a pool — across binders too: `k` and `j` occur free (declared by
/// `BINDER_VARS`) and bound, by binders of one or both. Integer division and
/// remainder appear with LITERAL non-zero divisors, so their
/// repeated-operand spellings are exercised without nonlinear queries.
struct Gen {
    rng: Rng,
    pools: HashMap<S, Vec<Formula>>,
}

/// The declarations of the binder variables where they occur free.
const BINDER_VARS: &str = "(declare-const k Int)\n(declare-const j Int)\n";

fn sym(name: &str) -> Formula {
    Formula::SymVar(Symbol::intern(name), Sort::Int)
}

impl Gen {
    fn make(&mut self, s: S, depth: u32, k: bool) -> Formula {
        if let Some(pool) = self.pools.get(&s)
            && !pool.is_empty()
            && self.rng.chance(1, 3)
        {
            let i = self.rng.below(pool.len());
            return pool[i].clone();
        }
        let f = if depth == 0 || self.rng.chance(1, 4) {
            self.leaf(s, k)
        } else {
            self.node(s, depth - 1, k)
        };
        self.pools.entry(s).or_default().push(f.clone());
        f
    }

    fn leaf(&mut self, s: S, k: bool) -> Formula {
        match s {
            S::Bool => match self.rng.below(4) {
                0 => Formula::Bool(self.rng.chance(1, 2)),
                1 => var("p", Sort::Bool),
                2 => var("q", Sort::Bool),
                // Both binder variables at once.
                _ => Formula::Lt(bx(sym("k")), bx(sym("j"))),
            },
            S::Int => match self.rng.below(4) {
                0 => Formula::Int(i128::from(u8::try_from(self.rng.below(7)).unwrap_or(0)) - 3),
                1 if k || self.rng.chance(2, 3) => sym(["k", "j"][self.rng.below(2)]),
                1 => sym("z"),
                _ => var(["x", "y"][self.rng.below(2)], Sort::Int),
            },
            S::Bv8 => match self.rng.below(3) {
                0 => Formula::BitVec {
                    value: i128::from(u8::try_from(self.rng.below(9)).unwrap_or(0)) - 4,
                    width: 8,
                },
                1 => var("a", Sort::BitVec(8)),
                _ => var("b", Sort::BitVec(8)),
            },
            S::Arr => match self.rng.below(2) {
                0 => Formula::const_array(Sort::Int, Sort::Int, Formula::Int(0)),
                _ => var("arr", Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))),
            },
        }
    }

    fn lit_divisor(&mut self) -> Box<Formula> {
        let d = [-3, -2, 2, 3, 5][self.rng.below(5)];
        bx(Formula::Int(d))
    }

    fn node(&mut self, s: S, d: u32, k: bool) -> Formula {
        match s {
            S::Bool => match self.rng.below(10) {
                0 => Formula::Not(bx(self.make(S::Bool, d, k))),
                1 => Formula::And(
                    (0..self.rng.below(4))
                        .map(|_| self.make(S::Bool, d, k))
                        .collect(),
                ),
                2 => Formula::Or(
                    (0..self.rng.below(4))
                        .map(|_| self.make(S::Bool, d, k))
                        .collect(),
                ),
                3 => Formula::Implies(bx(self.make(S::Bool, d, k)), bx(self.make(S::Bool, d, k))),
                4 => {
                    let (a, b) = (bx(self.make(S::Int, d, k)), bx(self.make(S::Int, d, k)));
                    match self.rng.below(5) {
                        0 => Formula::Eq(a, b),
                        1 => Formula::Lt(a, b),
                        2 => Formula::Le(a, b),
                        3 => Formula::Gt(a, b),
                        _ => Formula::Ge(a, b),
                    }
                }
                5 => {
                    let (a, b) = (bx(self.make(S::Bv8, d, k)), bx(self.make(S::Bv8, d, k)));
                    match self.rng.below(4) {
                        0 => Formula::BvULt(a, b, 8),
                        1 => Formula::BvULe(a, b, 8),
                        2 => Formula::BvSLt(a, b, 8),
                        _ => Formula::BvSLe(a, b, 8),
                    }
                }
                6 => {
                    let body = bx(self.make(S::Bool, d, true));
                    let bindings = match self.rng.below(3) {
                        0 => vec![(Symbol::intern("k"), Sort::Int)],
                        1 => vec![(Symbol::intern("j"), Sort::Int)],
                        _ => vec![
                            (Symbol::intern("k"), Sort::Int),
                            (Symbol::intern("j"), Sort::Int),
                        ],
                    };
                    if self.rng.chance(1, 2) {
                        Formula::Forall(bindings, body)
                    } else {
                        Formula::Exists(bindings, body)
                    }
                }
                7 => Formula::Ite(
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Bool, d, k)),
                ),
                8 => Formula::Eq(bx(self.make(S::Arr, d, k)), bx(self.make(S::Arr, d, k))),
                _ => Formula::Eq(bx(self.make(S::Bv8, d, k)), bx(self.make(S::Bv8, d, k))),
            },
            S::Int => match self.rng.below(9) {
                0 => Formula::Add(bx(self.make(S::Int, d, k)), bx(self.make(S::Int, d, k))),
                1 => Formula::Sub(bx(self.make(S::Int, d, k)), bx(self.make(S::Int, d, k))),
                2 => Formula::Mul(bx(self.make(S::Int, d, k)), bx(Formula::Int(3))),
                3 => Formula::Div(bx(self.make(S::Int, d, k)), self.lit_divisor()),
                4 => Formula::Rem(bx(self.make(S::Int, d, k)), self.lit_divisor()),
                5 => Formula::Neg(bx(self.make(S::Int, d, k))),
                6 => Formula::BvToInt(bx(self.make(S::Bv8, d, k)), 8, self.rng.chance(1, 2)),
                7 => Formula::Ite(
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Int, d, k)),
                    bx(self.make(S::Int, d, k)),
                ),
                _ => Formula::Select(bx(self.make(S::Arr, d, k)), bx(self.make(S::Int, d, k))),
            },
            S::Bv8 => {
                let a = bx(self.make(S::Bv8, d, k));
                match self.rng.below(12) {
                    0 => Formula::BvAdd(a, bx(self.make(S::Bv8, d, k)), 8),
                    1 => Formula::BvSub(a, bx(self.make(S::Bv8, d, k)), 8),
                    2 => Formula::BvMul(a, bx(self.make(S::Bv8, d, k)), 8),
                    3 => Formula::BvAnd(a, bx(self.make(S::Bv8, d, k)), 8),
                    4 => Formula::BvOr(a, bx(self.make(S::Bv8, d, k)), 8),
                    5 => Formula::BvXor(a, bx(self.make(S::Bv8, d, k)), 8),
                    6 => Formula::BvNot(a, 8),
                    7 => Formula::BvShl(a, bx(self.make(S::Bv8, d, k)), 8),
                    8 => Formula::BvLShr(a, bx(self.make(S::Bv8, d, k)), 8),
                    9 => Formula::BvExtract {
                        inner: bx(Formula::BvConcat(a, bx(self.make(S::Bv8, d, k)))),
                        high: 11,
                        low: 4,
                    },
                    10 => Formula::BvSignExt(
                        bx(Formula::BvExtract {
                            inner: a,
                            high: 6,
                            low: 0,
                        }),
                        1,
                    ),
                    _ => Formula::Ite(bx(self.make(S::Bool, d, k)), a, bx(self.make(S::Bv8, d, k))),
                }
            }
            S::Arr => match self.rng.below(3) {
                0 => Formula::Store(
                    bx(self.make(S::Arr, d, k)),
                    bx(self.make(S::Int, d, k)),
                    bx(self.make(S::Int, d, k)),
                ),
                1 => Formula::const_array(Sort::Int, Sort::Int, self.make(S::Int, d, k)),
                _ => Formula::Ite(
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Arr, d, k)),
                    bx(self.make(S::Arr, d, k)),
                ),
            },
        }
    }
}

fn random_corpus(seed: u64, n: usize, depth: u32) -> Vec<Formula> {
    let mut g = Gen {
        rng: Rng(seed),
        pools: HashMap::new(),
    };
    (0..n).map(|_| g.make(S::Bool, depth, false)).collect()
}

/// Random formulas: each `let` text is proved equal to its tree text, and
/// asserting either gives the same decided verdict.
#[test]
fn random_let_texts_are_proved_equal() {
    let corpus = random_corpus(0xa7_0001, 48, 5);
    let mut dag = FormulaDag::new();
    let mut with_lets = 0;
    let mut verdicts = Verdicts::default();
    for f in &corpus {
        let id = dag.intern(f);
        let tree = f.to_smtlib();
        let shared = dag.to_smtlib(id);
        if shared.contains("(let (") {
            with_lets += 1;
        }
        assert_eq!(
            differs(BINDER_VARS, &tree, &shared),
            Answer::Unsat,
            "\n  tree   {tree}\n  shared {shared}"
        );
        verdicts.compare(
            &assert_all(BINDER_VARS, std::slice::from_ref(&tree)),
            &assert_all(BINDER_VARS, std::slice::from_ref(&shared)),
            &shared,
        );
    }
    eprintln!(
        "{with_lets} of {} texts carry lets; verdicts {verdicts:?}",
        corpus.len()
    );
    assert!(
        with_lets >= corpus.len() / 3,
        "the corpus exercises sharing"
    );
    verdicts.assert_decided_floor(corpus.len() / 3);
}

/// Verdict agreement over decided rows only. Two `unknown`s (a timeout on
/// either side) prove nothing, so they are counted apart; a decided answer
/// on one side and `unknown` on the other is a timing difference, counted
/// too; two decided answers must be equal.
#[derive(Debug, Default)]
struct Verdicts {
    agreed: HashMap<String, usize>,
    undecided: usize,
}

impl Verdicts {
    fn compare(&mut self, tree: &Answer, shared: &Answer, text: &str) {
        let decided = |a: &Answer| matches!(a, Answer::Sat | Answer::Unsat);
        if decided(tree) && decided(shared) {
            assert_eq!(tree, shared, "verdicts differ\n  shared {text}");
            *self.agreed.entry(format!("{tree:?}")).or_default() += 1;
        } else {
            assert!(
                !matches!(tree, Answer::Refused(_)) && !matches!(shared, Answer::Refused(_)),
                "refused: tree {tree:?}, shared {shared:?}\n  shared {text}"
            );
            self.undecided += 1;
        }
    }

    fn assert_decided_floor(&self, floor: usize) {
        let decided: usize = self.agreed.values().sum();
        assert!(
            decided >= floor,
            "only {decided} rows were decided on both sides (floor {floor}): {self:?}"
        );
    }
}

/// Scripts of several assertions: under the definitions every term is proved
/// equal to its tree, and the whole script has the tree script's verdict.
#[test]
fn random_scripts_are_proved_equal() {
    let corpus = random_corpus(0xa7_0002, 40, 5);
    let mut dag = FormulaDag::new();
    let ids: Vec<NodeId> = corpus.iter().map(|f| dag.intern(f)).collect();
    let mut definitions = 0;
    let mut verdicts = Verdicts::default();
    for (chunk, formulas) in ids.chunks(4).zip(corpus.chunks(4)) {
        let script = dag.to_smtlib_script(chunk).expect("well-sorted roots");
        definitions += script.definitions.len();
        let defs: String = script
            .definitions
            .iter()
            .map(|d| format!("{d}\n"))
            .collect();
        let trees: Vec<String> = formulas.iter().map(Formula::to_smtlib).collect();
        for (tree, term) in trees.iter().zip(&script.terms) {
            assert_eq!(
                differs(&format!("{BINDER_VARS}{defs}"), tree, term),
                Answer::Unsat,
                "\n  defs {defs}\n  tree {tree}\n  term {term}"
            );
        }
        verdicts.compare(
            &assert_all(BINDER_VARS, &trees),
            &assert_all(&format!("{BINDER_VARS}{defs}"), &script.terms),
            &defs,
        );
    }
    eprintln!("{definitions} definitions; verdicts {verdicts:?}");
    assert!(definitions > 10, "the corpus exercises define-fun sharing");
    verdicts.assert_decided_floor(3);
}

/// The repeated-operand spellings (`Div`, `Rem`, signed `BvToInt`,
/// saturating `FpToSbv`/`FpToUbv`) bind a compound operand once; ay proves
/// the bound text equal to the tree text.
#[test]
fn repeated_operand_bindings_are_proved_equal() {
    let x = || var("x", Sort::Int);
    let big = Formula::Add(
        bx(x()),
        bx(Formula::Mul(bx(var("y", Sort::Int)), bx(Formula::Int(3)))),
    );
    let fa = || var("fa", Sort::Float { eb: 8, sb: 24 });
    let rne = || bx(Formula::FpRoundingMode(RoundingMode::RNE));
    let fbig = Formula::FpAdd(rne(), bx(fa()), bx(fa()));
    let cases = [
        Formula::Rem(bx(big.clone()), bx(Formula::Int(-7))),
        Formula::Div(bx(big), bx(Formula::Int(5))),
        Formula::BvToInt(
            bx(Formula::BvAdd(
                bx(var("a", Sort::BitVec(8))),
                bx(var("b", Sort::BitVec(8))),
                8,
            )),
            8,
            true,
        ),
        Formula::FpToSbv {
            rm: rne(),
            value: bx(fbig.clone()),
            width: 16,
            eb: 8,
            sb: 24,
        },
        Formula::FpToUbv {
            rm: rne(),
            value: bx(fbig),
            width: 16,
            eb: 8,
            sb: 24,
        },
    ];
    for f in &cases {
        let mut dag = FormulaDag::new();
        let id = dag.intern(f);
        let tree = f.to_smtlib();
        let shared = dag.to_smtlib(id);
        assert!(shared.starts_with("(let (("), "{shared}");
        assert_eq!(
            differs("", &tree, &shared),
            Answer::Unsat,
            "\n  tree   {tree}\n  shared {shared}"
        );
    }
}

/// The check is not vacuous: it refutes a binding hoisted across a binder
/// (which captures the bound name) and a swap of two bindings.
#[test]
fn the_equivalence_check_refutes_wrong_sharing() {
    // `(and p q)` outside the binder is about the declared `p`; inside
    // `forall ((p Bool))` it is about the bound one. The tree is `false`
    // (no `q` makes `p ∧ q` hold for every `p`); hoisting the binding out of
    // the binder would make it `p ∧ q`.
    let pq = Formula::And(vec![var("p", Sort::Bool), var("q", Sort::Bool)]);
    let f = Formula::And(vec![
        pq.clone(),
        Formula::forall(&[("p", Sort::Bool)], pq.clone()),
        pq,
    ]);
    let tree = f.to_smtlib();
    let mut dag = FormulaDag::new();
    let id = dag.intern(&f);
    let shared = dag.to_smtlib(id);
    assert_eq!(differs("", &tree, &shared), Answer::Unsat, "{shared}");
    assert!(
        shared.contains("(forall ((p Bool)) (and p q))"),
        "the binder keeps its own copy: {shared}"
    );
    let hoisted = "(let ((h (and p q))) (and h (forall ((p Bool)) h) h))";
    assert_eq!(
        differs("", &tree, hoisted),
        Answer::Sat,
        "capture is refuted"
    );

    let g = Formula::Lt(
        bx(Formula::Add(bx(var("x", Sort::Int)), bx(Formula::Int(1)))),
        bx(Formula::Add(bx(var("y", Sort::Int)), bx(Formula::Int(1)))),
    );
    let h = Formula::And(vec![g.clone(), g]);
    let swapped = "(let ((s (+ y 1)) (t (+ x 1))) (let ((u (< s t))) (and u u)))";
    assert_eq!(
        differs("", &h.to_smtlib(), swapped),
        Answer::Sat,
        "a swap is refuted"
    );
}

/// The shapes where a binding is moved across binders — a closed subterm
/// shared by several binder bodies, a subterm of `k` shared by two binders
/// of `j` inside `forall k`, shadowing, a binder that mentions an outer
/// binder's variable, nested binders over closed shared bodies, a closed
/// context under sibling binders, and the open chain that must be spelled
/// once per binder body — are each proved equal to their tree by ay, and
/// each really moves a binding (the text binds before a binder it uses it
/// under).
#[test]
fn hoisted_bindings_are_proved_equal() {
    let int = |name: &str| var(name, Sort::Int);
    let lt = |a: Formula, b: Formula| Formula::Lt(bx(a), bx(b));
    let gt0 = |a: Formula| Formula::Gt(bx(a), bx(Formula::Int(0)));
    let and = |v: Vec<Formula>| Formula::And(v);
    let forall = |n: &str, b: Formula| Formula::forall(&[(n, Sort::Int)], b);
    let exists = |n: &str, b: Formula| Formula::exists(&[(n, Sort::Int)], b);

    let closed = gt0(Formula::Add(bx(int("y")), bx(Formula::Int(1))));
    let m = Formula::Gt(bx(int("k")), bx(Formula::Int(1)));
    let open_binder = exists("j", lt(int("j"), int("k")));
    let mut cases: Vec<(&str, Formula)> = vec![
        (
            "closed subterm in sibling binder bodies",
            and(vec![
                closed.clone(),
                forall("x", and(vec![closed.clone(), gt0(int("x"))])),
                exists(
                    "x",
                    Formula::Or(vec![closed.clone(), lt(int("x"), int("y"))]),
                ),
            ]),
        ),
        (
            "a subterm of k shared by two binders of j",
            forall(
                "k",
                and(vec![
                    forall("j", and(vec![m.clone(), lt(int("j"), int("k"))])),
                    exists("j", Formula::Or(vec![m.clone(), gt0(int("j"))])),
                ]),
            ),
        ),
        (
            "shadowing",
            and(vec![
                m.clone(),
                m.clone(),
                forall(
                    "k",
                    and(vec![
                        m.clone(),
                        forall("k", and(vec![m.clone(), m.clone()])),
                    ]),
                ),
            ]),
        ),
        (
            "a binder open in an outer binder's variable",
            forall("k", and(vec![open_binder.clone(), open_binder])),
        ),
    ];
    // Nested binders over closed shared bodies (four levels).
    let (mut a, mut b) = (var("p", Sort::Bool), var("q", Sort::Bool));
    for i in 0..4 {
        let body = and(vec![a, b]);
        a = forall(&format!("x{i}"), body.clone());
        b = exists(&format!("w{i}"), body);
    }
    cases.push(("nested binders over closed bodies", and(vec![a, b])));
    // One closed context under four sibling binders.
    let ctx = Formula::Add(bx(Formula::Add(bx(int("x")), bx(int("y")))), bx(int("z")));
    cases.push((
        "a closed context under sibling binders",
        and((0..4)
            .map(|i| {
                let name = format!("u{i}");
                forall(&name, Formula::Ge(bx(ctx.clone()), bx(int(&name))))
            })
            .collect()),
    ));
    // The open chain: G_{i+1} = (and (forall k G_i) G_i).
    let mut g = gt0(int("k"));
    for _ in 0..4 {
        g = and(vec![forall("k", g.clone()), g]);
    }
    cases.push(("the open chain", g));

    let mut dag = FormulaDag::new();
    for (what, f) in &cases {
        let id = dag.intern(f);
        let tree = f.to_smtlib();
        let shared = dag.to_smtlib(id);
        assert!(
            shared.contains("(let (("),
            "{what}: something is bound: {shared}"
        );
        assert_eq!(
            differs(BINDER_VARS, &tree, &shared),
            Answer::Unsat,
            "{what}\n  tree   {tree}\n  shared {shared}"
        );
        // And as a script of the formula and its negation.
        let not = dag.intern(&Formula::Not(bx(f.clone())));
        let script = dag.to_smtlib_script(&[id, not]).expect("well-sorted");
        let defs: String = script
            .definitions
            .iter()
            .map(|d| format!("{d}\n"))
            .collect();
        assert_eq!(
            differs(&format!("{BINDER_VARS}{defs}"), &tree, &script.terms[0]),
            Answer::Unsat,
            "{what} (script)\n  defs {defs}\n  term {}",
            script.terms[0]
        );
    }
}

/// `define-fun` sorts are never guessed. ay refuses a definition declared
/// `Int` whose body is `Real` — and ACCEPTS one declared `Real` whose body
/// is `Int` (it coerces), so a wrongly guessed `Real` would not even be an
/// error. The script printer therefore refuses mixed `Int`/`Real` operands
/// (`DagError::UnsortedDefinition`) instead of picking one, and defines a
/// shared node whose operands agree. Pinned, so an ay bump that changes
/// either answer is seen here.
#[test]
fn define_fun_sorts_are_not_guessed() {
    let decl = witness_declarations();
    assert!(
        matches!(
            run(
                &format!("{decl}(define-fun d () Int (+ 1 r))\n(assert (= d d))\n"),
                Duration::from_secs(5)
            ),
            Answer::Refused(_)
        ),
        "ay refuses an Int-declared Real body"
    );
    assert!(
        !matches!(
            run(
                &format!("{decl}(define-fun d () Real (+ x 1))\n(assert (= d d))\n"),
                Duration::from_secs(5)
            ),
            Answer::Refused(_)
        ),
        "ay coerces an Int body declared Real (so a guessed Real is no error)"
    );

    let r = || bx(var("r", Sort::Real));
    let mixed = Formula::Add(bx(Formula::Int(1)), r());
    let a = Formula::Eq(bx(mixed.clone()), bx(Formula::rat_from_int(2)));
    let b = Formula::Not(bx(Formula::Eq(bx(mixed), bx(Formula::rat_from_int(0)))));
    let mut dag = FormulaDag::new();
    let (ia, ib) = (dag.intern(&a), dag.intern(&b));
    assert!(
        matches!(
            dag.to_smtlib_script(&[ia, ib]),
            Err(DagError::UnsortedDefinition { .. })
        ),
        "mixed Int/Real operands: no sort is guessed"
    );
    // Per assertion, `let` needs no sort: the same terms print and decide.
    let tree = a.to_smtlib();
    assert_eq!(differs("", &tree, &dag.to_smtlib(ia)), Answer::Unsat);

    let real = Formula::Add(r(), r());
    let c = Formula::Eq(bx(real.clone()), bx(Formula::rat_from_int(2)));
    let d = Formula::Not(bx(Formula::Eq(bx(real), bx(Formula::rat_from_int(0)))));
    let (ic, id) = (dag.intern(&c), dag.intern(&d));
    let script = dag.to_smtlib_script(&[ic, id]).expect("agreeing sorts");
    assert_eq!(script.definitions, ["(define-fun dag!0_0 () Real (+ r r))"]);
    let defs = format!("{}\n", script.definitions[0]);
    assert_eq!(
        differs(&defs, &c.to_smtlib(), &script.terms[0]),
        Answer::Unsat
    );
}
