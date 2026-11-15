// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// THE ACCEPTANCE CRITERION FOR THE TYPED VALUE MODEL — a falsification test.
// ══════════════════════════════════════════════════════════════════════════
//
// THE THESIS: put the encoding convention IN THE TYPE, so that dropping a fact
// yields TOP — and therefore a FAILED IMPLICATION at the consumption site —
// rather than a silent reinterpretation of the value under the raw convention.
//
// The thesis is tested against the two miscompiles that actually shipped in a
// consumer that hand-encodes every sum, product, function and set into
// anonymous i64 lanes and records which convention each lane obeys in a side
// map (`aggregate_shapes: HashMap<u8, AggregateShape>`). From that consumer's
// own fix comment: "Dropping the shape at a control-flow join therefore does
// NOT lose precision conservatively — it silently REINTERPRETS an index as a
// raw member value."
//
//   * FIXTURE-WP18 (index-vs-member): a union-key row off-by-one — an INDEX
//     used where a raw MEMBER was expected (node n where n-1 was meant).
//   * FIXTURE-WP28 (join-drop): at a control-flow join, two carriers over an
//     IDENTICAL universe that differed only in which proof cited them failed
//     to merge; the shape was dropped and the value reverted to the raw
//     convention. Caught only by a runtime differential, after 30,186
//     divergences.
//
// Both are pure trust-ir modules. No consumer change, no codegen, no solver —
// the lattice is DECIDABLE, which is why this file can prove anything at all
// on a box with no `ay`/`z3` binary on PATH.
//
// ── NON-VACUITY DISCIPLINE ────────────────────────────────────────────────
//
// A test that passes because nothing was checked is the failure mode this
// campaign's verifiers caught repeatedly. So every negative fixture below is
// paired with:
//
//   (a) a CONTROL module, structurally identical except that the required
//       predicate IS implied, which must validate with ZERO errors — proving
//       the module is well-formed and the failure is not incidental;
//   (b) a BASELINE module with the refinements stripped, which must validate
//       with ZERO errors — proving that the identical shape compiles today,
//       i.e. that the fixture reproduces a real miscompile rather than a
//       pre-existing type error; and
//   (c) an assertion on the EXACT error — one error, the right variant, the
//       right site, and both predicates named in the rendered message.

use trust_ir::inst::Inst;
use trust_ir::{Constant, FuncTy, Module, Pred, PredId, Space, Ty, TyId, Universe, ValueId};
use trust_ir_build::{ValidationError, validate_module};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// `m = 8`: the universe of union keys is `U = {1..=8}` (MEMBER space), so a
/// valid INDEX into it is `0..=7`. The off-by-one that shipped is exactly the
/// gap between those two ranges.
const M: i128 = 8;

/// Look a predicate up by CONTENT. Tests must never hardcode a table index:
/// the whole point of content-interning is that the id is a function of the
/// content, so that is how a test should ask for it.
fn pred_id(module: &Module, pred: &Pred) -> PredId {
    let i = module
        .predicates
        .iter()
        .position(|p| p == pred)
        .unwrap_or_else(|| panic!("predicate {pred} not interned in this module"));
    PredId::new(i as u32)
}

/// Look a `Pred::InUniverse` up by the universe's CONTENT and the space.
fn in_universe_id(module: &Module, universe: &Universe, space: Space) -> PredId {
    let u = module
        .universes
        .iter()
        .position(|x| x == universe)
        .unwrap_or_else(|| panic!("universe {universe} not interned in this module"));
    pred_id(
        module,
        &Pred::InUniverse(trust_ir::UnivId::new(u as u32), space),
    )
}

fn refinement_errors(module: &Module) -> Vec<ValidationError> {
    validate_module(module)
        .into_iter()
        .filter(|e| {
            matches!(
                e,
                ValidationError::RefinementNotImplied { .. }
                    | ValidationError::RefinementTypeInvalid { .. }
                    | ValidationError::PredicateTableMalformed { .. }
                    | ValidationError::PredicateTableNotInterned { .. }
                    | ValidationError::DanglingPredicateRef { .. }
            )
        })
        .collect()
}

/// Assert the module validates COMPLETELY clean — not merely free of
/// refinement errors. This is the non-vacuity anchor: it proves the fixture
/// modules are well-formed programs and the negative results below come from
/// the implication check and nothing else.
fn assert_validates_clean(module: &Module, what: &str) {
    let errors = validate_module(module);
    assert!(
        errors.is_empty(),
        "{what} must validate clean, got {} error(s): {}",
        errors.len(),
        errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("; ")
    );
}

/// Assert exactly one `RefinementNotImplied`, at `site`, naming both
/// predicates.
fn assert_single_named_implication_failure(
    module: &Module,
    site_fragment: &str,
    actual_fragment: &str,
    required_fragment: &str,
) -> String {
    let errors = validate_module(module);
    assert_eq!(
        errors.len(),
        1,
        "expected exactly one error (the named implication failure), got {}: {}",
        errors.len(),
        errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("; ")
    );
    let ValidationError::RefinementNotImplied {
        location,
        actual,
        required,
    } = &errors[0]
    else {
        panic!(
            "expected RefinementNotImplied (the consumption rule), got {:?}",
            errors[0]
        );
    };
    assert!(
        location.contains(site_fragment),
        "failure must be reported AT the consumption site; expected {site_fragment:?} in {location:?}"
    );
    assert!(
        actual.contains(actual_fragment),
        "the carried predicate must be NAMED; expected {actual_fragment:?} in {actual:?}"
    );
    assert!(
        required.contains(required_fragment),
        "the required predicate must be NAMED; expected {required_fragment:?} in {required:?}"
    );
    let rendered = errors[0].to_string();
    assert!(
        rendered.contains(actual) && rendered.contains(required),
        "the rendered diagnostic must carry both predicates: {rendered}"
    );
    rendered
}

/// A `RefinementType` obligation citing a predicate through the EXISTING
/// `ProofFormula` channel.
///
/// Reuse, not rebuild: `ObligationKind::RefinementType` already exists and is
/// already a contract kind, so it is the only replayable-authority path there
/// is. What was missing was never the consumption half — it was the carrier.
/// Two obligations minted here cite the SAME `PredId` from different proofs,
/// which is precisely the WP-28 setup.
fn cite_predicate(module: &mut Module, id: u32, pred: PredId, proof_name: &str) {
    use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
    let table = module.pred_table();
    let rendered = table.describe(pred);
    // The formula is rendered by trust-ir itself into the EXISTING carrier —
    // no second schema is invented for refinements.
    let formula = table.proof_formula(pred).expect("predicate is interned");
    module.proof_obligations.push(ProofObligation {
        id: trust_ir::ProofId::new(id),
        kind: ObligationKind::RefinementType,
        status: ProofStatus::Pending,
        description: format!("{proof_name} cites {rendered}"),
        formula: Some(formula),
        function: None,
        source: None,
        site: None,
        spec: None,
    });
}

// ---------------------------------------------------------------------------
// FIXTURE-WP18 — index-vs-member
// ---------------------------------------------------------------------------

/// How the value reaching the key-consumption site is described.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Carrier {
    /// The shipped bug's shape: a raw INDEX interval `[0, m]`. No convention
    /// is recorded — only a number.
    RawIndexInterval,
    /// The honest statement of the same value: an INDEX into `U`. This is the
    /// property that was NOT STATABLE in trust-ir at HEAD.
    IndexIntoUniverse,
    /// The correct carrier: a MEMBER of `U`.
    MemberOfUniverse,
    /// A STRONGER member fact: a member of a sub-universe of `U`. Must be
    /// ACCEPTED — proving `implies` is a real entailment check and not
    /// predicate equality in disguise.
    MemberOfSubUniverse,
    /// No refinement at all — the fact was never recorded. Must be REJECTED:
    /// absence is `top`.
    Unrefined,
}

/// `fn row_lookup(k) { call @key_of(k); ret }` where `@key_of`'s parameter
/// declares the key-consumption requirement `InUniverse(U, Member)`.
///
/// This is the WP-18 shape reduced to its essentials: a value described one
/// way flows into a site that demands another.
fn fixture_wp18(carrier: Carrier) -> Module {
    let mut m = Module::new("wp18_index_vs_member");

    // U = {1..=8}: the union-key universe (MEMBER space).
    let u = m
        .intern_universe(Universe::IntRange { lo: 1, hi: M })
        .expect("Module::intern_universe: test fixture")
        .expect("canonical");
    let required = m
        .intern_pred(Pred::InUniverse(u, Space::Member))
        .expect("Module::intern_pred: test fixture")
        .expect("in range");

    let i64_ty = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    let required_ty = Ty::Refine(i64_ty, required);

    let carrier_ty = match carrier {
        // `[0, m]` rather than `[0, m-1]`: the off-by-one exactly as it
        // shipped. Note the check does NOT depend on the off-by-one — see
        // `IndexIntoUniverse`, which is correctly bounded and still refused.
        Carrier::RawIndexInterval => {
            let p = m
                .intern_pred(Pred::Interval { lo: 0, hi: M })
                .expect("Module::intern_pred: test fixture")
                .expect("canonical");
            cite_predicate(&mut m, 0, p, "row-index proof");
            Ty::Refine(i64_ty, p)
        }
        Carrier::IndexIntoUniverse => {
            let p = m
                .intern_pred(Pred::InUniverse(u, Space::Index))
                .expect("Module::intern_pred: test fixture")
                .expect("in range");
            cite_predicate(&mut m, 0, p, "row-index proof");
            Ty::Refine(i64_ty, p)
        }
        Carrier::MemberOfUniverse => Ty::Refine(i64_ty, required),
        Carrier::MemberOfSubUniverse => {
            let sub = m
                .intern_universe(Universe::IntRange { lo: 2, hi: 5 })
                .expect("Module::intern_universe: test fixture")
                .expect("canonical");
            let p = m
                .intern_pred(Pred::InUniverse(sub, Space::Member))
                .expect("Module::intern_pred: test fixture")
                .expect("in range");
            Ty::Refine(i64_ty, p)
        }
        Carrier::Unrefined => Ty::I64,
    };

    cite_predicate(&mut m, 1, required, "key-consumption proof");
    build_call_pair(&mut m, carrier_ty, required_ty);
    m
}

/// The BASELINE: the identical program with every refinement stripped to the
/// base type. This is what trust-ir accepts at HEAD, and it is why the
/// miscompile was reachable — the property was not statable, so nothing could
/// reject it.
fn fixture_wp18_baseline() -> Module {
    let mut m = Module::new("wp18_baseline_no_refinements");
    build_call_pair(&mut m, Ty::I64, Ty::I64);
    m
}

/// `fn key_of(x: required_ty)` + `fn row_lookup(k: carrier_ty) { call @key_of(k) }`.
fn build_call_pair(m: &mut Module, carrier_ty: Ty, required_ty: Ty) {
    use trust_ir::node::InstrNode;
    use trust_ir::{Block, BlockId, FuncId, Function};

    let key_of_ty = m
        .add_func_type(FuncTy {
            params: vec![required_ty],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let row_lookup_ty = m
        .add_func_type(FuncTy {
            params: vec![carrier_ty.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut key_of = Function::new(FuncId::new(0), "key_of", key_of_ty, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((
        ValueId::new(0),
        m.func_types[key_of_ty.as_usize()].params[0].clone(),
    ));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    key_of.blocks.push(entry);
    m.functions.push(key_of);

    let mut row_lookup =
        Function::new(FuncId::new(1), "row_lookup", row_lookup_ty, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), carrier_ty));
    entry.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(0)],
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    row_lookup.blocks.push(entry);
    m.functions.push(row_lookup);
}

#[test]
fn wp18_raw_index_interval_into_a_member_site_fails_validation() {
    let m = fixture_wp18(Carrier::RawIndexInterval);

    // The lattice answer, independent of the validator.
    let carried = pred_id(&m, &Pred::Interval { lo: 0, hi: M });
    let required = in_universe_id(&m, &Universe::IntRange { lo: 1, hi: M }, Space::Member);
    let table = m.pred_table();
    assert!(
        !table.implies(carried, required),
        "in[0, {M}] must NOT imply membership of 1..={M} — 0 is not a member"
    );
    assert!(
        table.implies(required, carried),
        "but membership of 1..={M} DOES entail the numeric bound [0, {M}] — \
         the lattice is directional, not an equality check"
    );

    let rendered = assert_single_named_implication_failure(
        &m,
        "call @key_of arg 0",
        "in[0, 8]",
        "member of 1..=8",
    );
    assert!(
        rendered.contains("must FAIL here rather than be reinterpreted"),
        "{rendered}"
    );
}

#[test]
fn wp18_an_index_into_u_does_not_satisfy_a_member_site() {
    // THE STATEMENT THAT WAS NOT EXPRESSIBLE AT HEAD. Both carriers are over
    // the SAME universe and the same machine representation; only the
    // convention differs. Nothing about the i64 distinguishes them, which is
    // exactly why the fact has to live in the type.
    let m = fixture_wp18(Carrier::IndexIntoUniverse);

    let u = Universe::IntRange { lo: 1, hi: M };
    let as_index = in_universe_id(&m, &u, Space::Index);
    let as_member = in_universe_id(&m, &u, Space::Member);
    let table = m.pred_table();
    assert!(
        !table.implies(as_index, as_member),
        "index-into-U must NOT imply member-of-U"
    );
    assert!(!table.implies(as_member, as_index), "nor the converse");

    assert_single_named_implication_failure(
        &m,
        "call @key_of arg 0",
        "index into 1..=8",
        "member of 1..=8",
    );
}

#[test]
fn wp18_a_dropped_fact_is_top_and_fails_the_site() {
    // The unrefined carrier: the convention was never recorded. Under the old
    // regime this is what every lane looked like, and it compiled clean.
    let m = fixture_wp18(Carrier::Unrefined);
    let rendered = assert_single_named_implication_failure(
        &m,
        "call @key_of arg 0",
        "top (no refinement carried",
        "member of 1..=8",
    );
    assert!(rendered.contains("the fact was dropped"), "{rendered}");
}

#[test]
fn wp18_non_vacuity_the_correct_carrier_validates_clean() {
    // CONTROL (a): identical module, satisfiable requirement. If this failed,
    // the negative results above would prove nothing about the implication.
    assert_validates_clean(
        &fixture_wp18(Carrier::MemberOfUniverse),
        "wp18 with the correct member carrier",
    );
}

#[test]
fn wp18_non_vacuity_a_stronger_fact_is_accepted() {
    // CONTROL (a'): a member of {2..=5} IS a member of {1..=8}. Accepting this
    // proves `implies` is entailment, not predicate equality — a check that
    // only ever accepted identical ids would pass every negative test above
    // for the wrong reason.
    let m = fixture_wp18(Carrier::MemberOfSubUniverse);
    let sub = in_universe_id(&m, &Universe::IntRange { lo: 2, hi: 5 }, Space::Member);
    let whole = in_universe_id(&m, &Universe::IntRange { lo: 1, hi: M }, Space::Member);
    let table = m.pred_table();
    assert!(
        table.implies(sub, whole),
        "member of 2..=5 must imply member of 1..=8"
    );
    assert_validates_clean(&m, "wp18 with a strictly stronger member carrier");
}

#[test]
fn wp18_non_vacuity_the_baseline_shape_compiles_today() {
    // CONTROL (b): the identical program, unrefined, is accepted — which is
    // the whole problem. The fixture reproduces a MISCOMPILE, not a
    // pre-existing type error.
    assert_validates_clean(
        &fixture_wp18_baseline(),
        "the unrefined baseline (this is what ships the off-by-one)",
    );
}

// ---------------------------------------------------------------------------
// FIXTURE-WP28 — the join drop
// ---------------------------------------------------------------------------

/// What the two incoming edges of the control-flow join carry.
#[derive(Clone, Copy, PartialEq, Eq)]
enum JoinShape {
    /// Two carriers over an IDENTICAL universe, minted independently and cited
    /// by two different proofs. Content-interning must give them ONE id, so
    /// the join PRESERVES the fact.
    SameUniverseTwoProofs,
    /// Two carriers over an identical universe spelled two different (but
    /// extensionally equal) ways. Interning cannot collapse these — but
    /// `implies` decides them, so the fact is still preserved.
    SameUniverseTwoSpellings,
    /// Genuinely different universes. The join must weaken to TOP and then
    /// FAIL at the consumption site.
    DifferentUniverses,
    /// One edge carries the fact, the other does not. The exact shipped
    /// mechanism: the shape is dropped on one path and the value reverts to
    /// the raw convention.
    OneEdgeDroppedTheFact,
}

/// ```text
/// fn merge(c: bool, x: <edge-a ty>, y: <edge-b ty>)
///   bb0(c, x, y): condbr c -> bb1(x) / bb1(y)
///   bb1(k: refine<i64, required>): call @key_of(k); ret
/// ```
///
/// `bb1`'s parameter is the join, and its declared type is what the merge must
/// satisfy — the consumption site for BOTH incoming edges.
fn fixture_wp28(shape: JoinShape) -> Module {
    use trust_ir::node::InstrNode;
    use trust_ir::{Block, BlockId, FuncId, Function};

    let mut m = Module::new("wp28_join_drop");
    let i64_ty = m.add_type(Ty::I64).expect("Module::add_type: test fixture");

    // The universe every well-formed carrier on this path is over.
    let u = m
        .intern_universe(Universe::IntRange { lo: 1, hi: M })
        .expect("Module::intern_universe: test fixture")
        .expect("canonical");
    let required = m
        .intern_pred(Pred::InUniverse(u, Space::Member))
        .expect("Module::intern_pred: test fixture")
        .expect("in range");
    cite_predicate(&mut m, 0, required, "join-site proof");

    let (edge_a, edge_b) = match shape {
        JoinShape::SameUniverseTwoProofs => {
            // TWO INDEPENDENT MINTS. Two passes, two proofs, one universe.
            let a = m
                .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
                .expect("Module::intern_in_universe: test fixture")
                .expect("canonical");
            let b = m
                .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
                .expect("Module::intern_in_universe: test fixture")
                .expect("canonical");
            cite_predicate(&mut m, 1, a, "then-branch proof");
            cite_predicate(&mut m, 2, b, "else-branch proof");
            (Ty::Refine(i64_ty, a), Ty::Refine(i64_ty, b))
        }
        JoinShape::SameUniverseTwoSpellings => {
            let a = m
                .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
                .expect("Module::intern_in_universe: test fixture")
                .expect("canonical");
            let b = m
                .intern_in_universe(
                    Universe::Members((1..=M).map(Constant::Int).collect::<Vec<_>>()),
                    Space::Member,
                )
                .expect("Module::intern_in_universe: test fixture")
                .expect("canonical");
            (Ty::Refine(i64_ty, a), Ty::Refine(i64_ty, b))
        }
        JoinShape::DifferentUniverses => {
            let a = m
                .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
                .expect("Module::intern_in_universe: test fixture")
                .expect("canonical");
            let b = m
                .intern_in_universe(Universe::IntRange { lo: 100, hi: 200 }, Space::Member)
                .expect("Module::intern_in_universe: test fixture")
                .expect("canonical");
            cite_predicate(&mut m, 1, a, "then-branch proof");
            cite_predicate(&mut m, 2, b, "else-branch proof");
            (Ty::Refine(i64_ty, a), Ty::Refine(i64_ty, b))
        }
        JoinShape::OneEdgeDroppedTheFact => (Ty::Refine(i64_ty, required), Ty::I64),
    };

    let required_ty = Ty::Refine(i64_ty, required);
    let key_of_ty = m
        .add_func_type(FuncTy {
            params: vec![required_ty.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let merge_ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::Bool, edge_a.clone(), edge_b.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut key_of = Function::new(FuncId::new(0), "key_of", key_of_ty, BlockId::new(0));
    let mut kb = Block::new(BlockId::new(0));
    kb.params.push((ValueId::new(0), required_ty.clone()));
    kb.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    key_of.blocks.push(kb);
    m.functions.push(key_of);

    let mut merge = Function::new(FuncId::new(1), "merge", merge_ty, BlockId::new(0));
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
    merge.blocks.push(bb0);

    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((ValueId::new(3), required_ty));
    bb1.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(3)],
    }));
    bb1.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    merge.blocks.push(bb1);
    m.functions.push(merge);

    m
}

#[test]
fn wp28_content_interning_makes_two_proofs_agree_on_one_id() {
    // THE STRUCTURAL FIX. Two carriers over an identical universe, minted by
    // two independent passes and cited by two DIFFERENT proofs, are the SAME
    // PredId. The join therefore cannot fail to merge them, which is the exact
    // failure that shipped.
    let mut m = fixture_wp28(JoinShape::SameUniverseTwoProofs);

    assert_eq!(
        m.universes.len(),
        1,
        "one universe content must be one UnivId, however many passes minted it"
    );
    assert_eq!(
        m.predicates.len(),
        1,
        "one predicate content must be one PredId, however many proofs cite it"
    );

    // The citations genuinely differ; the identity does not.
    assert_eq!(m.proof_obligations.len(), 3);
    let cited: Vec<&str> = m
        .proof_obligations
        .iter()
        .map(|o| o.formula.as_ref().expect("formula").payload.as_str())
        .collect();
    assert_eq!(cited, vec!["pred.0", "pred.0", "pred.0"]);
    assert_ne!(
        m.proof_obligations[1].description, m.proof_obligations[2].description,
        "the two carriers really are cited by different proofs"
    );

    // The join PRESERVES the fact.
    let p = in_universe_id(&m, &Universe::IntRange { lo: 1, hi: M }, Space::Member);
    assert_eq!(
        m.join_preds(Some(p), Some(p))
            .expect("Module::join_preds: test fixture"),
        p,
        "joining a fact with itself must preserve it, not drop it"
    );

    assert_validates_clean(&m, "wp28 join over one interned universe");
}

#[test]
fn the_carrier_routes_through_the_existing_refinement_obligation_path() {
    // REUSE, NOT REBUILD. `ObligationKind::RefinementType` and `ProofFormula`
    // already existed and `RefinementType` is already a contract kind — the
    // only replayable-authority path there is. What was missing was never the
    // consumption half; it was the carrier. Here two DIFFERENT proofs cite the
    // SAME predicate through that one channel.
    let m = fixture_wp28(JoinShape::SameUniverseTwoProofs);
    let p = in_universe_id(&m, &Universe::IntRange { lo: 1, hi: M }, Space::Member);

    let citing = m.refinement_obligations_for(p);
    assert_eq!(
        citing.len(),
        3,
        "all three proofs must resolve to the one predicate"
    );
    for o in &citing {
        let f = o.formula.as_ref().expect("formula");
        assert_eq!(f.schema, trust_ir::pred::PRED_FORMULA_SCHEMA);
        assert_eq!(f.payload, format!("pred.{}", p.index()));
        assert_eq!(
            f.smtlib.as_deref(),
            Some("(and (<= 1 self) (<= self 8))"),
            "the predicate renders into SMT through the existing channel"
        );
    }

    // Authority is a SEPARATE question from validation, and it fails closed:
    // these obligations are `Pending` with no certificate, so nothing has
    // replayed authority. Validation still enforces the consumption rule
    // structurally — the lattice is decidable, so knowing that `top` does not
    // imply a membership convention needs no proof at all.
    assert!(
        !m.refinement_has_replayed_authority(p, &trust_ir::proof::RejectingProofAuthorityRechecker),
        "a Pending, uncertified obligation must not carry authority"
    );
    assert_validates_clean(&m, "an unproven-but-declared refinement still validates");
}

#[test]
fn wp28_two_spellings_of_one_universe_still_preserve_the_fact() {
    // Interning is syntactic on the canonical form, so `1..=8` and
    // `{1,...,8}` are two ids. `implies` decides them anyway — so the
    // structural fix and the decision procedure cover each other.
    let mut m = fixture_wp28(JoinShape::SameUniverseTwoSpellings);
    assert_eq!(m.universes.len(), 2, "two spellings, two universe entries");

    let a = in_universe_id(&m, &Universe::IntRange { lo: 1, hi: M }, Space::Member);
    let b = in_universe_id(
        &m,
        &Universe::Members((1..=M).map(Constant::Int).collect::<Vec<_>>()),
        Space::Member,
    );
    assert_ne!(a, b, "two spellings really are two ids");
    let table = m.pred_table();
    assert!(
        table.implies(a, b) && table.implies(b, a),
        "extensionally equal"
    );

    let required = a;
    let joined = m
        .join_preds(Some(a), Some(b))
        .expect("Module::join_preds: test fixture");
    assert!(
        m.pred_implies(Some(joined), Some(required)),
        "the join must still satisfy the site: the fact survived"
    );
    assert_validates_clean(&m, "wp28 join over two spellings of one universe");
}

#[test]
fn wp28_a_genuinely_different_universe_weakens_to_top_and_fails() {
    let mut m = fixture_wp28(JoinShape::DifferentUniverses);

    let a = in_universe_id(&m, &Universe::IntRange { lo: 1, hi: M }, Space::Member);
    let b = in_universe_id(&m, &Universe::IntRange { lo: 100, hi: 200 }, Space::Member);
    let required = a;

    // The join weakens to TOP — never to "one of them", which is what a
    // silent reinterpretation looks like.
    let joined = m
        .join_preds(Some(a), Some(b))
        .expect("Module::join_preds: test fixture");
    assert_eq!(
        m.predicates[joined.as_usize()],
        Pred::Top,
        "incomparable universes must merge to `top`, not to either arm"
    );
    assert!(
        !m.pred_implies(Some(joined), Some(required)),
        "and `top` must then fail the consumption site"
    );

    // And the validator says so at the join edge, naming both predicates.
    assert_single_named_implication_failure(
        &m,
        "bb0 -> bb1 join arg 0",
        "member of 100..=200",
        "member of 1..=8",
    );
}

#[test]
fn wp28_an_edge_that_dropped_the_fact_fails_instead_of_reverting() {
    // The shipped mechanism, verbatim: one path keeps the shape, one path
    // loses it. Previously the loss reinterpreted the value under the raw
    // convention and compiled. Now it is `top` at the join and it FAILS.
    let mut m = fixture_wp28(JoinShape::OneEdgeDroppedTheFact);

    let required = in_universe_id(&m, &Universe::IntRange { lo: 1, hi: M }, Space::Member);
    let joined = m
        .join_preds(Some(required), None)
        .expect("Module::join_preds: test fixture");
    assert_eq!(
        m.predicates[joined.as_usize()],
        Pred::Top,
        "joining a fact with an ABSENT fact must yield top, not the fact"
    );

    let rendered = assert_single_named_implication_failure(
        &m,
        "bb0 -> bb1 join arg 0",
        "top (no refinement carried",
        "member of 1..=8",
    );
    assert!(rendered.contains("the fact was dropped"), "{rendered}");
}

#[test]
fn wp28_non_vacuity_the_baseline_join_compiles_today() {
    // CONTROL (b) for the join fixture: the same control-flow shape with no
    // refinements anywhere validates clean. The join-drop was invisible
    // because there was nothing to drop.
    use trust_ir::node::InstrNode;
    use trust_ir::{Block, BlockId, FuncId, Function};

    let mut m = Module::new("wp28_baseline_no_refinements");
    let merge_ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::Bool, Ty::I64, Ty::I64],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut merge = Function::new(FuncId::new(0), "merge", merge_ty, BlockId::new(0));
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((ValueId::new(0), Ty::Bool));
    bb0.params.push((ValueId::new(1), Ty::I64));
    bb0.params.push((ValueId::new(2), Ty::I64));
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(0),
        then_target: BlockId::new(1),
        then_args: vec![ValueId::new(1)],
        else_target: BlockId::new(1),
        else_args: vec![ValueId::new(2)],
    }));
    merge.blocks.push(bb0);
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((ValueId::new(3), Ty::I64));
    bb1.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    merge.blocks.push(bb1);
    m.functions.push(merge);

    assert_validates_clean(&m, "the unrefined join baseline");
}

// ---------------------------------------------------------------------------
// Table well-formedness and the interning invariant
// ---------------------------------------------------------------------------

#[test]
fn a_duplicated_table_entry_is_rejected() {
    // The interning invariant is not merely a construction-time convention:
    // the validator re-derives it, so a decoded or hand-built module cannot
    // smuggle in the un-interned shape whose absence caused the join drop.
    let mut m = fixture_wp28(JoinShape::SameUniverseTwoProofs);
    let dup = m.predicates[0].clone();
    m.predicates.push(dup);

    let errors = refinement_errors(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::PredicateTableNotInterned {
                kind: "predicate",
                first: 0,
                duplicate: 1,
                ..
            }
        )),
        "expected a not-interned rejection, got: {errors:?}"
    );

    let mut m = fixture_wp28(JoinShape::SameUniverseTwoProofs);
    let dup = m.universes[0].clone();
    m.universes.push(dup);
    assert!(
        refinement_errors(&m).iter().any(|e| matches!(
            e,
            ValidationError::PredicateTableNotInterned {
                kind: "universe",
                ..
            }
        )),
        "duplicate universes must be rejected too"
    );
}

#[test]
fn malformed_table_entries_are_rejected() {
    let cases: Vec<(&str, Vec<Universe>, Vec<Pred>, &str)> = vec![
        (
            "inverted interval",
            vec![],
            vec![Pred::Interval { lo: 5, hi: 4 }],
            "inverted interval",
        ),
        (
            "unsorted finite set",
            vec![],
            vec![Pred::FiniteSet(vec![Constant::Int(3), Constant::Int(1)])],
            "canonical order",
        ),
        (
            "duplicated finite-set element",
            vec![],
            vec![Pred::FiniteSet(vec![Constant::Int(1), Constant::Int(1)])],
            "canonical order",
        ),
        (
            "non-scalar finite-set element",
            vec![],
            vec![Pred::FiniteSet(vec![Constant::Float(1.0)])],
            "total order",
        ),
        (
            "empty finite set",
            vec![],
            vec![Pred::FiniteSet(vec![])],
            "empty",
        ),
        (
            "inverted universe range",
            vec![Universe::IntRange { lo: 9, hi: 1 }],
            vec![],
            "inverted integer range",
        ),
        (
            "unary connective",
            vec![],
            vec![Pred::Top, Pred::Conj(vec![PredId::new(0)])],
            "operand(s)",
        ),
        (
            "unsorted connective",
            vec![],
            vec![
                Pred::Top,
                Pred::NonZero,
                Pred::Conj(vec![PredId::new(1), PredId::new(0)]),
            ],
            "strictly ascending",
        ),
    ];

    for (what, universes, predicates, fragment) in cases {
        let mut m = Module::new("malformed");
        m.universes = universes;
        m.predicates = predicates;
        let errors = refinement_errors(&m);
        assert!(
            errors.iter().any(
                |e| matches!(e, ValidationError::PredicateTableMalformed { detail, .. }
                    if detail.contains(fragment))
            ),
            "{what}: expected a malformed-table rejection mentioning {fragment:?}, got: {errors:?}"
        );
    }
}

#[test]
fn a_cardinality_blowup_is_rejected() {
    // A decidable lattice has to stay decidable in MICROSECONDS. An
    // enumeration past the cap is a producer bug (or a semantic constraint
    // smuggled in as an extension) and must be spelled as an interval.
    let cap = trust_ir::pred::MAX_ENUMERATED_MEMBERS;
    let oversized: Vec<Constant> = (0..=cap as i128).map(Constant::Int).collect();

    // The interning constructor refuses it outright — fail-closed at the door.
    let mut m = Module::new("blowup");
    assert!(
        m.intern_pred(Pred::FiniteSet(oversized.clone()))
            .expect("Module::intern_pred: test fixture")
            .is_none(),
        "intern_pred must refuse an over-cap extension rather than truncate it"
    );
    assert!(
        m.intern_universe(Universe::Members(oversized.clone()))
            .expect("Module::intern_universe: test fixture")
            .is_none(),
        "intern_universe must refuse it too"
    );
    assert!(m.predicates.is_empty() && m.universes.is_empty());

    // And a hand-built / decoded table carrying one is rejected by the
    // validator, so the door is not the only guard.
    let mut m = Module::new("blowup_decoded");
    m.predicates = vec![Pred::FiniteSet(oversized)];
    let errors = refinement_errors(&m);
    assert!(
        errors.iter().any(
            |e| matches!(e, ValidationError::PredicateTableMalformed { detail, .. }
                if detail.contains("over the") && detail.contains("cap"))
        ),
        "expected a cardinality-blowup rejection, got: {errors:?}"
    );
}

#[test]
fn implies_is_fast_enough_to_run_at_every_consumption_site() {
    // "Decidable" is worth nothing if it is not also CHEAP: the consumption
    // rule runs at every typed dataflow site in the module, so a solver-shaped
    // cost would make it unshippable. This is a floor, not a benchmark.
    let mut m = Module::new("speed");
    let big: Vec<Constant> = (0..1024).map(Constant::Int).collect();
    let a = m
        .intern_pred(Pred::FiniteSet(big.iter().take(512).cloned().collect()))
        .expect("Module::intern_pred: test fixture")
        .expect("canonical");
    let b = m
        .intern_pred(Pred::FiniteSet(big))
        .expect("Module::intern_pred: test fixture")
        .expect("canonical");
    let table = m.pred_table();

    let start = std::time::Instant::now();
    let iterations = 1000;
    for _ in 0..iterations {
        assert!(table.implies(a, b));
        assert!(!table.implies(b, a));
    }
    let per_call = start.elapsed() / (2 * iterations);
    assert!(
        per_call < std::time::Duration::from_millis(1),
        "implies took {per_call:?} per call over 512-of-1024-member sets; \
         the lattice must decide in microseconds, with no solver"
    );
}

#[test]
fn a_cyclic_or_forward_child_reference_is_rejected() {
    // Interning is append-only, so a child is always older than its parent.
    // Enforcing it is what makes the predicate graph acyclic BY CONSTRUCTION,
    // which is what lets the decision procedures terminate.
    let mut m = Module::new("cyclic");
    m.predicates = vec![
        Pred::Conj(vec![PredId::new(1), PredId::new(2)]),
        Pred::Top,
        Pred::NonZero,
    ];
    let errors = refinement_errors(&m);
    assert!(
        errors.iter().any(
            |e| matches!(e, ValidationError::PredicateTableMalformed { detail, .. }
                if detail.contains("strictly older"))
        ),
        "expected an acyclicity rejection, got: {errors:?}"
    );
}

#[test]
fn dangling_references_are_rejected() {
    let mut m = Module::new("dangling");
    m.predicates = vec![Pred::InUniverse(trust_ir::UnivId::new(7), Space::Member)];
    assert!(
        refinement_errors(&m).iter().any(|e| matches!(
            e,
            ValidationError::DanglingPredicateRef {
                kind: "univ",
                id: 7,
                ..
            }
        )),
        "a dangling UnivId must be rejected"
    );

    let mut m = Module::new("dangling_pred");
    m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    m.add_type(Ty::Refine(TyId::new(0), PredId::new(4)))
        .expect("Module::add_type: test fixture");
    assert!(
        refinement_errors(&m).iter().any(|e| matches!(
            e,
            ValidationError::DanglingPredicateRef {
                kind: "pred",
                id: 4,
                ..
            }
        )),
        "a dangling PredId in a Ty::Refine must be rejected"
    );
}

#[test]
fn nested_refinements_and_unstateable_predicates_are_rejected() {
    // One refinement layer per spelling: nesting would give one fact two
    // spellings and break interning as an identity.
    let mut m = Module::new("nested");
    let p = m
        .intern_pred(Pred::NonZero)
        .expect("Module::intern_pred: test fixture")
        .expect("leaf");
    let i64_ty = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    let inner = m
        .add_type(Ty::Refine(i64_ty, p))
        .expect("Module::add_type: test fixture");
    m.add_type(Ty::Refine(inner, p))
        .expect("Module::add_type: test fixture");
    assert!(
        refinement_errors(&m).iter().any(|e| matches!(
            e,
            ValidationError::RefinementTypeInvalid { detail, .. } if detail.contains("do not nest")
        )),
        "nested refinements must be rejected"
    );

    // `nonnull` is a pointer fact; an integer carrier cannot state it.
    let mut m = Module::new("unstateable");
    let p = m
        .intern_pred(Pred::NonNull)
        .expect("Module::intern_pred: test fixture")
        .expect("leaf");
    let i64_ty = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    m.add_type(Ty::Refine(i64_ty, p))
        .expect("Module::add_type: test fixture");
    assert!(
        refinement_errors(&m).iter().any(|e| matches!(
            e,
            ValidationError::RefinementTypeInvalid { detail, .. }
                if detail.contains("pointer-like base")
        )),
        "a predicate that cannot be stated about the base must be rejected"
    );
}

#[test]
fn a_body_may_not_assume_more_than_its_signature_guarantees() {
    // The entry block BINDS the caller-supplied values, so it is a consumption
    // site and the direction matters: a signature promising a raw interval
    // cannot satisfy an entry parameter that declares a membership convention.
    // Getting this backwards would let a function help itself to a convention
    // nobody established — which is the miscompile, wearing a different hat.
    use trust_ir::node::InstrNode;
    use trust_ir::{Block, BlockId, FuncId, Function};

    let mut m = Module::new("entry_direction");
    let i64_ty = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    let weak = m
        .intern_pred(Pred::Interval { lo: 1, hi: M })
        .expect("Module::intern_pred: test fixture")
        .expect("canonical");
    let strong = m
        .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
        .expect("Module::intern_in_universe: test fixture")
        .expect("canonical");

    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::Refine(i64_ty, weak)],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    // The body claims MORE than the signature promises.
    b.params.push((ValueId::new(0), Ty::Refine(i64_ty, strong)));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    m.functions.push(f);

    assert_single_named_implication_failure(&m, "entry param 0", "in[1, 8]", "member of 1..=8");

    // And the sound direction — a signature promising membership satisfying a
    // body that only needs the interval — validates clean.
    let mut m = Module::new("entry_direction_ok");
    let i64_ty = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    let weak = m
        .intern_pred(Pred::Interval { lo: 1, hi: M })
        .expect("Module::intern_pred: test fixture")
        .expect("canonical");
    let strong = m
        .intern_in_universe(Universe::IntRange { lo: 1, hi: M }, Space::Member)
        .expect("Module::intern_in_universe: test fixture")
        .expect("canonical");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::Refine(i64_ty, strong)],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::Refine(i64_ty, weak)));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    m.functions.push(f);
    assert_validates_clean(&m, "a body assuming less than its signature promises");
}

#[test]
fn representation_disagreement_is_reported_as_a_type_error_not_an_implication_one() {
    // A refinement never changes the representation, so a base mismatch is a
    // plain type error and must be reported as one — not laundered through the
    // predicate lattice.
    use trust_ir::node::InstrNode;
    use trust_ir::{Block, BlockId, FuncId, Function};

    let mut m = Module::new("repr_mismatch");
    let p = m
        .intern_pred(Pred::NonZero)
        .expect("Module::intern_pred: test fixture")
        .expect("leaf");
    let i64_ty = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    let i32_ty = m.add_type(Ty::I32).expect("Module::add_type: test fixture");

    let callee_ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::Refine(i32_ty, p)],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::Refine(i64_ty, p)],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut callee = Function::new(FuncId::new(0), "callee", callee_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::Refine(i32_ty, p)));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    callee.blocks.push(b);
    m.functions.push(callee);

    let mut caller = Function::new(FuncId::new(1), "caller", caller_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::Refine(i64_ty, p)));
    b.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(0)],
    }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(b);
    m.functions.push(caller);

    let errors = refinement_errors(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::RefinementTypeInvalid { detail, .. }
                if detail.contains("representation i64 does not match")
        )),
        "expected a representation mismatch, got: {errors:?}"
    );
}
