-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- The PREDICATE LATTICE of the v30 typed value model.
-- Mirrors: crates/trust-ir/src/pred.rs
--
-- STATUS: machine-checked as part of the `trust_ir-semantics` `lake build`.
-- The corresponding soundness theorems and their axiom-budget guards live in
-- TrustIr/Proofs/PredLatticeProps.lean and TrustIr/Proofs/AxiomAudit.lean.

import TrustIr.Basic
import TrustIr.Constant
import TrustIr.State.ValueMap

namespace TrustIr

/-!
# The predicate lattice (v30 typed value model)

The Lean model of `crates/trust-ir/src/pred.rs`: the decidable predicate
lattice that lets an encoding CONVENTION live in the type (`Ty.Refine`)
instead of in a producer-side map.

## Why a Lean model at all

`Ty.Refine` landed as a coordinated Rust/Lean triple, but the LATTICE was
unmodelled, so the consumption rule
(`trust-ir-build/src/validate.rs::check_refinement_consumption`) rested on an
unverified claim: that `implies` answers `true` only when the implication
genuinely holds. If `implies` ever certifies an implication that does not
hold, a convention mismatch passes validation silently — which is exactly the
shipped miscompile class (an INDEX read as a MEMBER).

This file gives the lattice a DENOTATION `⟦p⟧ : Value → Prop`;
`TrustIr/Proofs/PredLatticeProps.lean` proves against it:

* `impliesFuel_sound` — `implies a b = true → ∀ v, ⟦a⟧ v → ⟦b⟧ v`;
* `join_upper_bound_left` / `join_upper_bound_right` — the join is above both;
* `denote_Top` — `⟦top⟧ v` for every `v`, so a MISSING predicate is genuinely
  the weakest fact and licenses nothing;
* `index_never_implies_member` — the miscompile class, as a theorem.

## Model-vs-Rust fidelity, and the direction that matters

The transfer we need is **`Rust implies = true ⟹ Lean implies = true`**: only
then does the Lean soundness theorem cover every implication the Rust
validator actually certifies. So every deliberate divergence below leaves the
LEAN side *more permissive*, or is an exact mirror — never less permissive.
Each one, argued:

1. **Ids vs trees.** Rust interns predicates in a module table and spells
   `Conj`/`Disj` children as `PredId`s; here children are inline. The
   validator (`validate_refinement_tables`) enforces that a child id is
   STRICTLY OLDER than its parent, so a validated table is acyclic and
   denotes exactly one tree — `PredTable.resolve` below is that unfolding.
   A DANGLING id answers `false` in Rust and has no tree here at all; `false`
   is the conservative side, so the direction holds.
2. **Depth cap.** Rust's `implies_at` gives up (answers `false`) past
   `MAX_PRED_DEPTH = 64`; modelled exactly, as `fuel`. Soundness is proved
   for EVERY fuel, so the cap cannot matter to the theorem: Rust's budget is
   one particular fuel.
3. **Cardinality overflow.** Rust's `Universe::cardinality` answers `none`
   when the count does not fit `u128`, and `interval_bound_at` answers `none`
   when `card - 1` does not fit `i128`. Lean `Nat`/`Int` are unbounded, so
   this model answers `some` there — the permissive side.
4. **Binary vs linear search.** Rust decides extension membership by binary
   search; this model scans. On a canonical extension (the only kind the
   validator admits) the answers coincide.
5. **Structural equality.** Rust's `a == b` is derived `PartialEq`, which can
   compare non-scalar constants (floats, bytes, aggregates); `Pred.beq` here
   compares extension elements by `constantKey`, which is `none` for exactly
   those, so it answers `false` where Rust might answer `true`. The validator
   REJECTS a non-scalar element inside any extension (`members_defect`), so on
   a validated module the two agree. This is the one divergence that is not
   unconditionally on the permissive side, and it is bounded by validation —
   recorded here as a residual rather than hidden.
-/

/-- Recursion budget of the decision procedures. Mirrors Rust
    `MAX_PRED_DEPTH` (pred.rs). -/
def maxPredDepth : Nat := 64

/-- Extension-size cap. Mirrors Rust `MAX_ENUMERATED_MEMBERS`. -/
def maxEnumeratedMembers : Nat := 4096

/-- Connective arity cap. Mirrors Rust `MAX_CONNECTIVE_ARITY`. -/
def maxConnectiveArity : Nat := 64

/-! ## Space -/

/-- Which **encoding convention** an integer carrier obeys with respect to a
    universe. Mirrors Rust `trust_ir::pred::Space`.

    This is the distinction that makes the index-vs-member miscompile class
    EXPRESSIBLE: both spaces are carried by the same machine integer, so
    nothing about the representation distinguishes them — which is precisely
    why the fact has to live in the type. -/
inductive Space where
  /-- 0-based ordinal INDEX into the universe's canonical member ordering:
      `0 ≤ self < |U|`. NOT a claim of membership. -/
  | Index  : Space
  /-- MEMBER of the universe: `self ∈ U`. -/
  | Member : Space
  deriving DecidableEq, Repr, BEq, Hashable

/-! ## Constant keys -/

/-- Total ordering key of a scalar constant. Mirrors Rust `constant_key`:
    `Int → (0, v)`, `Bool → (1, v as i128)`, everything else `none`. Floats
    are excluded deliberately (NaN has no total order, and a lattice that
    silently ordered it would be unsound at exactly one input). -/
def constantKey : Constant → Option (Nat × Int)
  | .int v  => some (0, v)
  | .bool b => some (1, if b then 1 else 0)
  | _       => none

/-- Strict lexicographic order on keys (Rust tuple `Ord`). -/
def keyLt (a b : Nat × Int) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- Are the keys strictly ascending after `prev`, and is every element keyed
    at all? Mirrors the loop in Rust `members_are_canonical`. -/
def keysAscending : Option (Nat × Int) → List Constant → Bool
  | _, [] => true
  | prev, c :: rest =>
    match constantKey c with
    | none => false
    | some k =>
      match prev with
      | none => keysAscending (some k) rest
      | some p => if keyLt p k then keysAscending (some k) rest else false

/-- Is `items` a canonical extension: non-empty, in-cap, all-scalar, strictly
    ascending by `constantKey`? Mirrors Rust `members_are_canonical`. -/
def membersAreCanonical (items : List Constant) : Bool :=
  !items.isEmpty && items.length ≤ maxEnumeratedMembers && keysAscending none items

/-- Does an extension contain the given key? Mirrors Rust
    `members_contain_key` (binary search there, a scan here — the same answer
    on a canonical extension; fidelity note 4). -/
def membersContainKey (items : List Constant) (k : Nat × Int) : Bool :=
  items.any (fun c => constantKey c == some k)

/-- The integer payload of a constant, when it has one. -/
def constInt : Constant → Option Int
  | .int n => some n
  | _      => none

/-- Widen `(n, n)` by every integer constant in the list; `none` if any
    element is not an integer constant. -/
def intBoundsAux (n : Int) : List Constant → Option (Int × Int)
  | []        => some (n, n)
  | c :: rest =>
    match constInt c with
    | none => none
    | some k =>
      match intBoundsAux k rest with
      | none => none
      | some (lo, hi) => some (min n lo, max n hi)

/-- Tightest inclusive integer bounds over a list; `none` unless the list is
    non-empty and every element is an integer constant. -/
def intBoundsOf : List Constant → Option (Int × Int)
  | []        => none
  | c :: rest =>
    match constInt c with
    | none => none
    | some n => intBoundsAux n rest

/-- Tightest inclusive integer bounds over an extension, or `none` when it is
    non-canonical or not purely integral. Mirrors Rust `members_int_bounds`. -/
def membersIntBounds (items : List Constant) : Option (Int × Int) :=
  if membersAreCanonical items then intBoundsOf items else none

/-- Is every element of `a` also in `b` (by key)? `false` whenever either side
    is non-canonical — undecided means no implication. Mirrors Rust
    `members_subset`. -/
def membersSubset (a b : List Constant) : Bool :=
  membersAreCanonical a && membersAreCanonical b &&
    a.all (fun c => match constantKey c with
                    | some k => membersContainKey b k
                    | none   => false)

/-- `count` consecutive integers beginning at `lo`. Keeping the arithmetic in
    `Int` avoids an unproved Nat-to-Int coercion inside the executable model. -/
def intRangeFrom (lo : Int) : Nat → List Int
  | 0 => []
  | count + 1 => lo :: intRangeFrom (lo + 1) count

/-- `[lo, hi]` as a list of integers (empty when `lo > hi`). -/
def intRangeList (lo hi : Int) : List Int :=
  if lo > hi then [] else intRangeFrom lo ((hi - lo).toNat + 1)

/-- Does a canonical extension contain every integer in `[lo, hi]`? Mirrors
    Rust `members_contain_interval`, including its "interval wider than the
    extension ⇒ undecided" guard. -/
def membersContainInterval (items : List Constant) (lo hi : Int) : Bool :=
  if lo > hi then true
  else
    membersAreCanonical items &&
      !(items.length ≤ (hi - lo).toNat) &&
      (intRangeList lo hi).all (fun n => membersContainKey items (0, n))

/-- Sorted, deduplicating insertion by key. -/
def insertByKey (c : Constant) : List Constant → List Constant
  | [] => [c]
  | d :: rest =>
    match constantKey c, constantKey d with
    | some kc, some kd =>
      if kc == kd then d :: rest
      else if keyLt kc kd then c :: d :: rest
      else d :: insertByKey c rest
    -- Unreachable on any extension `canonicalizeMembers` admits (it rejects
    -- unkeyed elements up front); keeping BOTH sides here is what makes
    -- `mem_insertByKey` unconditional.
    | _, _ => c :: d :: rest

/-- Sort + dedup an extension into canonical order. `none` if any element is
    non-scalar, or the canonical result is empty / over cap. Mirrors Rust
    `canonicalize_members`. -/
def canonicalizeMembers (items : List Constant) : Option (List Constant) :=
  if items.all (fun c => (constantKey c).isSome) then
    let sorted := items.foldr insertByKey []
    if sorted.isEmpty || maxEnumeratedMembers < sorted.length then none else some sorted
  else none

/-! ## Universe -/

/-- A finite universe: the extension a `Space` is interpreted against.
    Mirrors Rust `trust_ir::Universe`.

    Identity is CONTENT, and content only — no name, no provenance, no citing
    proof id. Two universes with the same extension are the same universe,
    which is the structural fix for the join-drop miscompile. -/
inductive Universe where
  /-- Inclusive contiguous integer range `{lo, …, hi}`. Well-formed iff
      `lo ≤ hi`. -/
  | IntRange : Int → Int → Universe
  /-- Explicit member list in canonical order. -/
  | Members  : List Constant → Universe
  deriving Repr

/-- Number of members. Mirrors Rust `Universe::cardinality` (which
    additionally answers `none` on `u128` overflow — fidelity note 3). -/
def Universe.cardinality : Universe → Option Nat
  | .IntRange lo hi => if lo ≤ hi then some ((hi - lo).toNat + 1) else none
  | .Members items  => if membersAreCanonical items then some items.length else none

/-- Structural well-formedness. Mirrors Rust `Universe::is_canonical`. -/
def Universe.isCanonical : Universe → Bool
  | .IntRange lo hi => lo ≤ hi
  | .Members items  => membersAreCanonical items

/-- Does this universe contain every integer in `[lo, hi]`? Mirrors Rust
    `Universe::contains_interval`. -/
def Universe.containsInterval : Universe → Int → Int → Bool
  | .IntRange ulo uhi, lo, hi =>
    if lo > hi then true else ulo ≤ uhi && ulo ≤ lo && hi ≤ uhi
  | .Members items, lo, hi => membersContainInterval items lo hi

/-- Is every member of `self` also a member of `other`? Mirrors Rust
    `Universe::is_subset_of`. -/
def Universe.isSubsetOf : Universe → Universe → Bool
  | .IntRange lo hi, .IntRange olo ohi => lo ≤ hi && olo ≤ lo && hi ≤ ohi
  | .IntRange lo hi, .Members items    => lo ≤ hi && membersContainInterval items lo hi
  | .Members items, .IntRange lo hi    =>
    membersAreCanonical items && lo ≤ hi &&
      items.all (fun c => match constInt c with
                          | some v => lo ≤ v && v ≤ hi
                          | none   => false)
  | .Members a, .Members b => membersSubset a b

/-- Tightest inclusive integer interval containing every member. Mirrors Rust
    `Universe::integer_bounds`. -/
def Universe.integerBounds : Universe → Option (Int × Int)
  | .IntRange lo hi => if lo ≤ hi then some (lo, hi) else none
  | .Members items  => membersIntBounds items

/-- The module's content-interned universe table (the `universes` slice a Rust
    `PredTable` carries). -/
abbrev UnivTable := List Universe

/-- Resolve a universe id; `none` for a dangling id. -/
def UnivTable.get? (U : UnivTable) (u : UnivId) : Option Universe :=
  trustIrListGet? U u.index

/-! ## Pred -/

/-- A decidable predicate over ONE distinguished free variable — `self`, the
    refined value. Mirrors Rust `trust_ir::Pred` constructor for constructor
    (`Conj`/`Disj` children are inline here rather than `PredId`s; fidelity
    note 1).

    The lattice order is implication: `a ⊑ b` iff `Pred.implies a b`. `Top` is
    the greatest element ("no information", where a lost fact lands) and
    `Bottom` the least ("unsatisfiable"). -/
inductive Pred where
  /-- `lo ≤ self ≤ hi`. A RAW NUMERIC fact: it carries no `Space` and must
      never imply `InUniverse _ Member` by accident. -/
  | Interval   : Int → Int → Pred
  /-- `self ∈ {c₀, c₁, …}`, a canonical extension. -/
  | FiniteSet  : List Constant → Pred
  /-- The convention carrier: `self` is an INDEX into, or a MEMBER of, `u`. -/
  | InUniverse : UnivId → Space → Pred
  /-- `self ≠ 0`. -/
  | NonZero    : Pred
  /-- `self` is not the null pointer. -/
  | NonNull    : Pred
  /-- All of the listed predicates hold. -/
  | Conj       : List Pred → Pred
  /-- At least one of the listed predicates holds. -/
  | Disj       : List Pred → Pred
  /-- NO INFORMATION. Where a dropped fact lands. -/
  | Top        : Pred
  /-- Unsatisfiable; implies everything vacuously. -/
  | Bottom     : Pred
  deriving Repr

/-! ### Decidable structural equality

`Constant` has no `DecidableEq` in this model (Lean `Float` has none), so
extension elements are compared by `constantKey` — exact on every extension
the validator admits (fidelity note 5). -/

/-- Key-level constant equality: `false` whenever either side is unkeyed. -/
def constBeq (c d : Constant) : Bool :=
  match constantKey c, constantKey d with
  | some k1, some k2 => k1 == k2
  | _, _ => false

/-- Pointwise list equality under `constBeq`. -/
def constListBeq : List Constant → List Constant → Bool
  | [], [] => true
  | c :: cs, d :: ds => constBeq c d && constListBeq cs ds
  | _, _ => false

/-- Content equality of canonical universes. Mirrors Rust's derived
    `PartialEq` on `Universe`; keyed constant equality is exact on every
    member list accepted by the validator (fidelity note 5). -/
def Universe.beq : Universe → Universe → Bool
  | .IntRange alo ahi, .IntRange blo bhi => alo == blo && ahi == bhi
  | .Members a, .Members b => constListBeq a b
  | _, _ => false

mutual

/-- Structural equality of predicates. -/
def Pred.beq : Pred → Pred → Bool
  | .Interval a b, .Interval c d => a == c && b == d
  | .FiniteSet x, .FiniteSet y => constListBeq x y
  | .InUniverse u1 s1, .InUniverse u2 s2 => (u1.index = u2.index) && (s1 = s2)
  | .NonZero, .NonZero => true
  | .NonNull, .NonNull => true
  | .Conj x, .Conj y => Pred.listBeq x y
  | .Disj x, .Disj y => Pred.listBeq x y
  | .Top, .Top => true
  | .Bottom, .Bottom => true
  | _, _ => false

/-- Pointwise list equality of predicates. -/
def Pred.listBeq : List Pred → List Pred → Bool
  | [], [] => true
  | p :: ps, q :: qs => Pred.beq p q && Pred.listBeq ps qs
  | _, _ => false

end

/-! ## The denotation `⟦·⟧`

This is the point of the file: it says, in Lean, exactly what `pred.rs`
documents each constructor to MEAN. The soundness theorem is stated against
this, so auditing the claim reduces to auditing the denotation. -/

/-- How a constant matches a runtime value.

    Keyed constants (`Int`, `Bool` — the only ones the validator admits inside
    an extension) get their exact meaning: an integer constant matches an
    integer value of that numeric value AT ANY WIDTH (a predicate constrains
    the number, not the carrier width); a bool constant matches that bool.

    Every other constant is handed to the parameter `m`. The decision
    procedures never look inside one (`constantKey` is `none` there, and every
    arm answers `false`), so the theorems are proved for an ARBITRARY `m`,
    universally quantified: nothing may depend on its shape. -/
def constDenote (m : Constant → Value → Prop) : Constant → Value → Prop
  | .int n, v  => ∃ w, v = .int w n
  | .bool b, v => v = .bool b
  | c, v       => m c v

/-- `self ∈ U`. -/
def Universe.contains (m : Constant → Value → Prop) : Universe → Value → Prop
  | .IntRange lo hi, v => ∃ w n, v = .int w n ∧ lo ≤ n ∧ n ≤ hi
  | .Members items, v  => ∃ c ∈ items, constDenote m c v

mutual

/-- `⟦p⟧ v` — the denotation of a predicate at a runtime value.

    * `Interval lo hi` — `v` is an integer in `[lo, hi]`;
    * `FiniteSet items` — `v` matches one of the listed constants;
    * `InUniverse u Index` — `v` is an integer with `0 ≤ v < |U|` (**the
      ordinal**, not a member);
    * `InUniverse u Member` — `v ∈ U`;
    * `NonZero` — `v` is a nonzero integer;
    * `NonNull` — `v` is not the null pointer;
    * `Conj` / `Disj` — the connectives;
    * `Top` — TRUE (no information: this is why a dropped fact licenses
      nothing);
    * `Bottom` — FALSE.

    A DANGLING universe id denotes `False`: an unresolvable fact is not a
    fact. Every Rust arm that would consult it answers `false`, so this
    cannot open a gap. -/
def Pred.denote (U : UnivTable) (m : Constant → Value → Prop) : Pred → Value → Prop
  | .Interval lo hi, v => ∃ w n, v = .int w n ∧ lo ≤ n ∧ n ≤ hi
  | .FiniteSet items, v => ∃ c ∈ items, constDenote m c v
  | .InUniverse u s, v =>
    match UnivTable.get? U u with
    | none => False
    | some univ =>
      match s with
      | .Member => Universe.contains m univ v
      | .Index =>
        match univ.cardinality with
        | none => False
        | some k => ∃ w n, v = .int w n ∧ 0 ≤ n ∧ n < (k : Int)
  | .NonZero, v => ∃ w n, v = .int w n ∧ n ≠ 0
  | .NonNull, v => v ≠ .nullPtr
  | .Conj cs, v => Pred.denoteAll U m cs v
  | .Disj cs, v => Pred.denoteAny U m cs v
  | .Top, _ => True
  | .Bottom, _ => False

/-- Conjunction over a child list. -/
def Pred.denoteAll (U : UnivTable) (m : Constant → Value → Prop) :
    List Pred → Value → Prop
  | [], _ => True
  | p :: rest, v => Pred.denote U m p v ∧ Pred.denoteAll U m rest v

/-- Disjunction over a child list. -/
def Pred.denoteAny (U : UnivTable) (m : Constant → Value → Prop) :
    List Pred → Value → Prop
  | [], _ => False
  | p :: rest, v => Pred.denote U m p v ∨ Pred.denoteAny U m rest v

end

/-! ## The decision procedures -/

/-- Intersection of a list of bounds (no emptiness filter: the caller applies
    Rust's single final `lo ≤ hi` check). -/
def intersectBounds : List (Int × Int) → Option (Int × Int)
  | []        => none
  | [b]       => some b
  | b :: rest =>
    match intersectBounds rest with
    | none => none
    | some (lo, hi) => some (max b.1 lo, min b.2 hi)

/-- Convex hull of a list of bounds. -/
def hullBounds : List (Int × Int) → Option (Int × Int)
  | []        => none
  | [b]       => some b
  | b :: rest =>
    match hullBounds rest with
    | none => none
    | some (lo, hi) => some (min b.1 lo, max b.2 hi)

/-- Keep the bounds that exist (the `Conj` arm's "a conjunct with no bound
    contributes nothing"). -/
def filterSomeBounds : List (Option (Int × Int)) → List (Int × Int)
  | []             => []
  | none :: rest   => filterSomeBounds rest
  | some b :: rest => b :: filterSomeBounds rest

/-- Require every bound to exist (the `Disj` arm's "a hull is sound only if
    EVERY arm has a bound"). -/
def sequenceBounds : List (Option (Int × Int)) → Option (List (Int × Int))
  | []             => some []
  | none :: _      => none
  | some b :: rest => (sequenceBounds rest).map (fun bs => b :: bs)

/-- The interval a predicate pins `self` to, when it pins one at all.

    SOUND DIRECTION: `some (lo, hi)` means the predicate ENTAILS
    `lo ≤ self ≤ hi`. `none` means "no interval fact is available" — never
    "unbounded is fine". Mirrors Rust `interval_bound_at`, with `fuel`
    standing for `MAX_PRED_DEPTH - depth`. -/
def Pred.intervalBoundFuel (U : UnivTable) : Nat → Pred → Option (Int × Int)
  | 0, _ => none
  | _ + 1, .Interval lo hi => if lo ≤ hi then some (lo, hi) else none
  | _ + 1, .FiniteSet items => membersIntBounds items
  | _ + 1, .InUniverse u .Member =>
    match UnivTable.get? U u with
    | none => none
    | some univ => univ.integerBounds
  | _ + 1, .InUniverse u .Index =>
    match UnivTable.get? U u with
    | none => none
    | some univ =>
      match univ.cardinality with
      | none => none
      | some k => if k = 0 then none else some (0, (k : Int) - 1)
  | fuel + 1, .Conj cs =>
    match intersectBounds (filterSomeBounds
        (cs.map (fun p => Pred.intervalBoundFuel U fuel p))) with
    | none => none
    | some (lo, hi) => if lo ≤ hi then some (lo, hi) else none
  | fuel + 1, .Disj cs =>
    match sequenceBounds (cs.map (fun p => Pred.intervalBoundFuel U fuel p)) with
    | none => none
    | some bs => hullBounds bs
  -- Bottom is unsatisfiable, so it entails every interval; a degenerate one
  -- is reported so containment checks succeed vacuously.
  | _ + 1, .Bottom => some (0, 0)
  | _ + 1, .NonZero => none
  | _ + 1, .NonNull => none
  | _ + 1, .Top => none

/-- Does `a` entail `b`?

    **Decidable, total, and sound in the only direction that matters: `true`
    is returned ONLY when the implication genuinely holds; every undecided
    case answers `false`.**

    Mirrors Rust `implies_at` ARM FOR ARM, in the same observable order. The
    sufficient `Disj`-on-the-right rule deliberately precedes the exhaustive
    `Disj`-on-the-left rule, so containment such as
    `(a ∨ b) → (a ∨ b ∨ c)` is recognized before the left shape can commit
    the decision. -/
def Pred.impliesFuel (U : UnivTable) : Nat → Pred → Pred → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    match a, b with
    -- Bottom entails everything; nothing but Bottom entails Bottom.
    | .Bottom, _ => true
    | _, .Bottom => false
    -- Everything entails Top.
    | _, .Top => true
    -- A Top carrier entails no non-trivial fact — THE LOAD-BEARING `false` of
    -- the whole design: it is what turns a dropped fact into a loud failure
    -- at the consumption site instead of a silent reinterpretation.
    | .Top, _ => false
    | a, b =>
      -- Interning makes syntactic identity the common fast path — and it is
      -- also the structural fix for the join-drop class.
      if Pred.beq a b then true
      -- Conjunction on the LEFT: any conjunct suffices (fall through).
      else if (match a with
               | .Conj cs => cs.any (fun c => Pred.impliesFuel U fuel c b)
               | _ => false) then true
      -- Disjunction on the RIGHT: one arm suffices (fall through). This
      -- sufficient rule must run before the exhaustive Disj-on-the-left rule,
      -- exactly as in Rust; otherwise a disjunction that contains `a` can be
      -- missed merely because `a` is itself a disjunction.
      else if (match b with
               | .Disj cs => cs.any (fun c => Pred.impliesFuel U fuel a c)
               | _ => false) then true
      else
        match b with
        -- Conjunction on the RIGHT: every conjunct must be entailed.
        | .Conj cs => cs.all (fun c => Pred.impliesFuel U fuel a c)
        | _ =>
          match a with
          -- Disjunction on the LEFT: every arm must entail the target.
          | .Disj cs => cs.all (fun c => Pred.impliesFuel U fuel c b)
          | _ =>
              match b with
              -- ── The convention rule ─────────────────────────────────────
              | .InUniverse ub sb =>
                match a with
                | .InUniverse ua sa =>
                  -- DIFFERENT SPACE OVER THE SAME UNIVERSE IS NOT AN
                  -- IMPLICATION. This single `false` is what makes the
                  -- index-vs-member miscompile class statable and catchable.
                  if sa ≠ sb then false
                  else
                    match UnivTable.get? U ua, UnivTable.get? U ub with
                    | some ua', some ub' =>
                      match sa with
                      -- Membership is monotone in the universe.
                      | .Member => ua'.isSubsetOf ub'
                      -- Index-hood is extensional in the universe: an ordinal
                      -- into one ordering cannot be consumed as an ordinal
                      -- into another merely because the cardinalities agree.
                      | .Index => Universe.beq ua' ub'
                    | _, _ => false
                -- No other fact shape entails a universe claim: an interval
                -- is a raw numeric fact and carries no convention, which is
                -- exactly why it must not be promoted into one.
                | _ => false
              -- ── Numeric containment ─────────────────────────────────────
              | .Interval lo hi =>
                match Pred.intervalBoundFuel U fuel a with
                | some (alo, ahi) => lo ≤ alo && ahi ≤ hi
                | none => false
              | .FiniteSet target =>
                match a with
                | .FiniteSet src => membersSubset src target
                | .Interval lo hi => membersContainInterval target lo hi
                | .InUniverse u s =>
                  match UnivTable.get? U u with
                  | none => false
                  | some univ =>
                    match s with
                    | .Member =>
                      match univ with
                      | .Members src => membersSubset src target
                      | .IntRange lo hi => membersContainInterval target lo hi
                    | .Index =>
                      match univ.cardinality with
                      | none => false
                      | some k =>
                        if k = 0 then false
                        else membersContainInterval target 0 ((k : Int) - 1)
                | _ => false
              -- ── NonZero / NonNull ───────────────────────────────────────
              -- A numeric fact entails NonZero when 0 is outside its bounds.
              | .NonZero =>
                match Pred.intervalBoundFuel U fuel a with
                | some (lo, hi) => 0 < lo || hi < 0
                | none => false
              -- NonNull is a POINTER fact, entailed only by itself (handled
              -- by `Pred.beq` above) — deliberately NOT derived from NonZero,
              -- because "not the null pointer" and "not the integer zero"
              -- coincide only under a provenance assumption this lattice does
              -- not make.
              | .NonNull => false
              | .Top => false
              | .Bottom => false
              | .Conj _ => false
              | .Disj _ => false

/-- `implies` at the Rust budget. Soundness is proved for EVERY fuel, so this
    choice is a completeness/performance knob, never a soundness one. -/
def Pred.implies (U : UnivTable) (a b : Pred) : Bool :=
  Pred.impliesFuel U (maxPredDepth + 1) a b

/-- **The join**: the least upper bound this lattice can compute for two facts
    meeting at a control-flow join. Mirrors Rust `join_pred`.

    Join is DISJUNCTION, and every fallback is toward `Top` — never toward
    `Bottom`, never toward "unknown but assume ok". The result is always
    weaker than or equal to both inputs, so a merge can only LOSE information,
    and losing it makes the consumption site FAIL rather than reinterpret. -/
def Pred.join (U : UnivTable) (a b : Pred) : Pred :=
  if Pred.beq a b then a
  else if Pred.implies U a b then b
  else if Pred.implies U b a then a
  else
    match a, b with
    | .Interval alo ahi, .Interval blo bhi => .Interval (min alo blo) (max ahi bhi)
    | .FiniteSet x, .FiniteSet y =>
      match canonicalizeMembers (x ++ y) with
      | some items => .FiniteSet items
      -- Over cap / non-scalar: weaken, do not guess.
      | none => .Top
    -- Incomparable universes: two different universes share no convention a
    -- consumer can act on, so decaying to Top makes the loss loud.
    | .InUniverse _ _, .InUniverse _ _ => .Top
    | a, b => .Disj [a, b]

/-- The consumption rule's reading of an ABSENT predicate: `Top`. Mirrors Rust
    `Module::pred_implies`, where `None` on either side is `top` — the whole
    design in one line. A dropped fact becomes `Top`, and `Top` entails
    nothing non-trivial, so the consumption site FAILS instead of
    reinterpreting the carrier. -/
def Pred.impliesOpt (U : UnivTable) (a b : Option Pred) : Bool :=
  match b with
  | none => true
  | some b' =>
    match a with
    | none => Pred.implies U .Top b'
    | some a' => Pred.implies U a' b'

/-! ## The interned table, and its unfolding into this model

Rust spells `Conj`/`Disj` children as `PredId`s into a content-interned module
table. `PredTable.resolve` is the unfolding of such a table into the tree
model above. It is TOTAL (fuel-bounded) and SUCCEEDS on every table the
validator admits, because `validate_refinement_tables` enforces that a child
id is strictly older than its parent — which is exactly the fuel bound
`id.index + 1`. -/

/-- A predicate table entry: the id-spelled shape Rust stores. -/
inductive PredEntry where
  | Interval   : Int → Int → PredEntry
  | FiniteSet  : List Constant → PredEntry
  | InUniverse : UnivId → Space → PredEntry
  | NonZero    : PredEntry
  | NonNull    : PredEntry
  | Conj       : List PredId → PredEntry
  | Disj       : List PredId → PredEntry
  | Top        : PredEntry
  | Bottom     : PredEntry
  deriving Repr

/-- The module's content-interned predicate table. -/
abbrev PredTable := List PredEntry

/-- Require every child to resolve. -/
def sequencePreds : List (Option Pred) → Option (List Pred)
  | []             => some []
  | none :: _      => none
  | some p :: rest => (sequencePreds rest).map (fun ps => p :: ps)

/-- Unfold a table entry into the tree model. `none` for a dangling id, or for
    a table whose child ids are not strictly older (which the validator
    rejects as "the predicate graph must be acyclic by construction"). -/
def PredTable.resolveFuel (T : PredTable) : Nat → Nat → Option Pred
  | 0, _ => none
  | fuel + 1, i =>
    match trustIrListGet? T i with
    | none => none
    | some e =>
      match e with
      | .Interval lo hi => some (.Interval lo hi)
      | .FiniteSet items => some (.FiniteSet items)
      | .InUniverse u s => some (.InUniverse u s)
      | .NonZero => some .NonZero
      | .NonNull => some .NonNull
      | .Top => some .Top
      | .Bottom => some .Bottom
      | .Conj cs =>
        (sequencePreds (cs.map (fun c => PredTable.resolveFuel T fuel c.index))).map Pred.Conj
      | .Disj cs =>
        (sequencePreds (cs.map (fun c => PredTable.resolveFuel T fuel c.index))).map Pred.Disj

/-- Resolve an id at the fuel the validator's acyclicity invariant licenses. -/
def PredTable.resolve (T : PredTable) (p : PredId) : Option Pred :=
  PredTable.resolveFuel T (p.index + 1) p.index

/-! ## Executable fixtures

These mirror the Rust unit tests in `pred.rs` one for one, as `#guard`s: a
Lean build FAILS if the model's answers drift from the documented behaviour.
They are also the cheapest available cross-check that the Lean and Rust
decision procedures agree on the cases that carry the design. -/

private def u18 : UnivTable := [.IntRange 1 8]
private def uPair : UnivTable := [.IntRange 1 4, .IntRange 1 8]

-- top_implies_nothing_but_top
#guard Pred.implies [] .Top .Top = true
#guard Pred.implies [] .Top (.Interval 0 7) = false
#guard Pred.implies [] (.Interval 0 7) .Top = true

-- bottom_implies_everything
#guard Pred.implies [] .Bottom (.Interval 0 7) = true
#guard Pred.implies [] (.Interval 0 7) .Bottom = false

-- interval_containment_is_decided
#guard Pred.implies [] (.Interval 2 5) (.Interval 0 7) = true
#guard Pred.implies [] (.Interval 0 7) (.Interval 2 5) = false

-- finite_set_subset_is_decided
#guard Pred.implies [] (.FiniteSet [.int 1, .int 3]) (.FiniteSet [.int 1, .int 2, .int 3]) = true
#guard Pred.implies [] (.FiniteSet [.int 1, .int 2, .int 3]) (.FiniteSet [.int 1, .int 3]) = false

-- index_does_not_imply_member_over_the_same_universe (THE miscompile class)
#guard Pred.implies u18 (.InUniverse ⟨0⟩ .Index) (.InUniverse ⟨0⟩ .Member) = false
#guard Pred.implies u18 (.InUniverse ⟨0⟩ .Member) (.InUniverse ⟨0⟩ .Index) = false

-- raw_interval_never_promotes_to_a_membership_convention
#guard Pred.implies u18 (.Interval 1 8) (.InUniverse ⟨0⟩ .Member) = false
#guard Pred.implies u18 (.InUniverse ⟨0⟩ .Member) (.Interval 1 8) = true

-- member_is_monotone_but_index_is_extensional_in_the_universe
#guard Pred.implies uPair (.InUniverse ⟨0⟩ .Member) (.InUniverse ⟨1⟩ .Member) = true
#guard Pred.implies uPair (.InUniverse ⟨1⟩ .Member) (.InUniverse ⟨0⟩ .Member) = false
#guard Pred.implies uPair (.InUniverse ⟨0⟩ .Index) (.InUniverse ⟨1⟩ .Index) = false
#guard Pred.implies uPair (.InUniverse ⟨1⟩ .Index) (.InUniverse ⟨0⟩ .Index) = false

-- nonzero_is_entailed_only_when_zero_is_excluded
#guard Pred.implies [] (.Interval 1 4) .NonZero = true
#guard Pred.implies [] (.Interval 0 4) .NonZero = false

-- nonnull_is_not_derived_from_nonzero
#guard Pred.implies [] .NonZero .NonNull = false
#guard Pred.implies [] .NonNull .NonZero = false

-- conjunction_and_disjunction_are_decided
#guard Pred.implies [] (.Conj [.Interval 0 3, .Interval 2 9]) (.Interval 0 3) = true
#guard Pred.implies [] (.Disj [.Interval 0 3, .Interval 2 9]) (.Interval 0 9) = true
#guard Pred.implies [] (.Disj [.Interval 0 3, .Interval 2 9]) (.Interval 0 3) = false
#guard Pred.implies [] (.Interval 0 3) (.Disj [.Interval 0 3, .Interval 2 9]) = true

-- G4: the sufficient Disj-on-the-right rule runs before exhaustive
-- Disj-on-the-left, so a disjunction entails a larger disjunction that
-- literally contains it as an arm.
#guard Pred.implies [] (.Disj [.Top, .Interval 0 1])
  (.Disj [.Bottom, .Disj [.Top, .Interval 0 1]]) = true

-- an ABSENT predicate is Top, and Top licenses nothing
#guard Pred.impliesOpt u18 none (some (.InUniverse ⟨0⟩ .Member)) = false
#guard Pred.impliesOpt u18 (some (.InUniverse ⟨0⟩ .Member)) none = true

-- join stays above both inputs
#guard Pred.beq (Pred.join [] (.Interval 0 3) (.Interval 7 9)) (.Interval 0 9) = true
#guard Pred.beq (Pred.join uPair (.InUniverse ⟨0⟩ .Member) (.InUniverse ⟨1⟩ .Member))
        (.InUniverse ⟨1⟩ .Member) = true

end TrustIr
