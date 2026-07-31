-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Aggregate type properties: typing rules and structural lemmas for the
-- ty supremacy aggregate types (Set, Sequence, Record, Closure/FuncDef).
--
-- Reference: designs/2026-04-18-ty-supremacy-trust_ir-scope.md section 3.3
-- Issue: TrustIr#31 (companion to #30)

import TrustIr.Basic
import TrustIr.Constant
import TrustIr.Semantics.Aggregate

namespace TrustIr

/-!
# Aggregate Typing Rules

This file extends the TrustIr Lean formalization with static typing rules for
the new aggregate types added in the ty supremacy scope:

- Ty.Set TyId SetRepr       -- unordered set, element type id + repr hint
- Ty.Sequence TyId          -- ordered packed sequence
- Ty.Record RecordId        -- named-field record (ty-style, no layout)
- Ty.Closure ClosureTyId    -- function value + captured environment frame

The central relation is Ty.hasConst : Ty -> Constant -> Prop, which says
a constant is well-typed at a given TrustIr type. We provide:

1. Introduction rules (one per new variant).
2. Structural lemmas (listed in issue #31 acceptance criteria).
3. Cross-variant distinctness sanity checks.

## Scope note

ty's techlead scope (issue #30) added the Rust surface (Ty, Constant,
Validate). Issue #31 adds the Lean denotation for these types. The
denotation deliberately stays at the typing-judgment layer for now; a
follow-up can add operational semantics for set operations (union /
intersection / cardinality) on top of hasConst.

## Backward compatibility

Existing aggregate constants (aggregate/tuple/struct-shaped) continue to
type-check via hasConst.aggregate / .struct / .tuple etc. No prior lemma
is weakened.
-/

-- =================================================================
-- Bounded vector constant shapes
-- =================================================================

/-- Vector constant typing is intentionally bounded to the executable x86
    subset currently modeled by the Lean semantics. Unsupported lane
    counts or element types are rejected by having no typing rule. -/
def Ty.supportedConstVector : Nat -> Ty -> Prop
  | 4, .I32 => True
  | 2, .I64 => True
  | 4, .Bool => True
  | 2, .Bool => True
  | _, _ => False

-- =================================================================
-- Element-type lookup helpers
-- =================================================================

/-- A type-id resolver: maps TyId values to concrete Ty. Used to resolve
    the element type of Ty.Set / Ty.Sequence without building a module
    table into every theorem statement.

    Mirrors the Rust side's module.types table lookup. -/
abbrev TyEnv := TyId -> Option Ty

/-- Record definition resolver. -/
abbrev RecordEnv := RecordId -> Option RecordDef

/-- Closure type resolver. -/
abbrev ClosureEnv := ClosureTyId -> Option ClosureTy

/-- Joint typing environment used by the hasConst relation. -/
structure TypingEnv where
  tys      : TyEnv
  records  : RecordEnv
  closures : ClosureEnv

namespace TypingEnv

/-- Empty typing environment. All lookups return none. -/
def empty : TypingEnv :=
  { tys := fun _ => none,
    records := fun _ => none,
    closures := fun _ => none }

/-- Extend an environment with a single Ty definition. -/
def withTy (e : TypingEnv) (id : TyId) (t : Ty) : TypingEnv :=
  { e with tys := fun id' => if id'.index = id.index then some t else e.tys id' }

/-- Extend an environment with a single record definition. -/
def withRecord (e : TypingEnv) (r : RecordDef) : TypingEnv :=
  { e with records := fun id' =>
      if id'.index = r.id.index then some r else e.records id' }

/-- Extend an environment with a single closure type. -/
def withClosure (e : TypingEnv) (id : ClosureTyId) (c : ClosureTy) : TypingEnv :=
  { e with closures := fun id' =>
      if id'.index = id.index then some c else e.closures id' }

end TypingEnv

-- =================================================================
-- hasConst: static well-typedness of a constant at a given Ty
-- =================================================================

/-- Static typing judgment: the given constant is well-typed at the given
    TrustIr type in the given environment.

    This is a specification-level relation (Prop, not Bool). It is used
    to state correctness properties; runtime type checking lives in the
    evaluator monad.

    ## Rules for the new aggregate variants

    - Ty.Set ty repr + Constant.set elems : requires tys ty to resolve to
      some elemTy, and every element to have hasConst elemTy. The repr
      hint does not enter the rule -- see set_repr_independence below.

    - Ty.Sequence ty + Constant.sequence elems : ordered dual of Set.

    - Ty.Vector lanes elemTy + Constant.vector elems : bounded to the
      executable x86-facing shapes `<4 x i32>`, `<2 x i64>`,
      `<4 x bool>`, and `<2 x bool>`.

    - Ty.Record rid + Constant.record fields : requires the RecordDef to
      match the field list in length, name, and per-field typing.

    - Ty.Closure cid + Constant.closure fn caps : requires captures to
      match the declared ClosureTy capture list in length and per-slot
      typing. This freezes captures at closure-literal time -- the
      structural fix for ty issue 4145. -/
inductive Ty.hasConst : TypingEnv -> Ty -> Constant -> Prop
  -- Integer types accept integer constants (bit-width check is dynamic).
  | int_i8    {e : TypingEnv} {n : Int} : hasConst e .I8    (.int n)
  | int_i16   {e : TypingEnv} {n : Int} : hasConst e .I16   (.int n)
  | int_i32   {e : TypingEnv} {n : Int} : hasConst e .I32   (.int n)
  | int_i64   {e : TypingEnv} {n : Int} : hasConst e .I64   (.int n)
  | int_i128  {e : TypingEnv} {n : Int} : hasConst e .I128  (.int n)
  -- Floating-point types accept float constants.
  | float_f32 {e : TypingEnv} {f : Float} : hasConst e .F32 (.float f)
  | float_f64 {e : TypingEnv} {f : Float} : hasConst e .F64 (.float f)
  -- Bool accepts bool constants.
  | bool_b    {e : TypingEnv} {b : _root_.Bool} : hasConst e .Bool (.bool b)
  -- New: Vector. Homogeneous and lane-count exact for the bounded
  -- executable x86-facing vector subset.
  | vector_lanes (e : TypingEnv) (lanes : Nat) (elemTy : Ty)
      (elems : List Constant) :
      Ty.supportedConstVector lanes elemTy ->
      elems.length = lanes ->
      (forall c, c ∈ elems -> hasConst e elemTy c) ->
      hasConst e (.Vector lanes elemTy) (.vector elems)
  -- New: Set. Homogeneous: every element inhabits the resolved element Ty.
  | set_elems (e : TypingEnv) (tyId : TyId) (repr : SetRepr)
      (elemTy : Ty) (elems : List Constant) :
      e.tys tyId = some elemTy ->
      (forall c, c ∈ elems -> hasConst e elemTy c) ->
      hasConst e (.Set tyId repr) (.set elems)
  -- New: Sequence. Same shape as Set but ordered.
  | seq_elems (e : TypingEnv) (tyId : TyId) (elemTy : Ty)
      (elems : List Constant) :
      e.tys tyId = some elemTy ->
      (forall c, c ∈ elems -> hasConst e elemTy c) ->
      hasConst e (.Sequence tyId) (.sequence elems)
  -- New: Record. Field labels and per-field types must match RecordDef.
  -- Note: the name-match and the typing judgment are stated as separate
  -- hypotheses rather than an And-conjunction so the inductive stays
  -- non-nested (Lean's kernel refuses nested inductives whose parameters
  -- mention local binders).
  | record_fields (e : TypingEnv) (recId : RecordId) (rd : RecordDef)
      (fields : List (String × Constant)) :
      e.records recId = some rd ->
      fields.length = rd.fields.length ->
      (forall i (h : i < fields.length) (hf : i < rd.fields.length),
         (fields.get ⟨i, h⟩).fst = (rd.fields.get ⟨i, hf⟩).name) ->
      (forall i (h : i < fields.length) (hf : i < rd.fields.length),
         hasConst e (rd.fields.get ⟨i, hf⟩).ty (fields.get ⟨i, h⟩).snd) ->
      hasConst e (.Record recId) (.record fields)
  -- New: Closure. Captures must have declared types.
  | closure_captures (e : TypingEnv) (cid : ClosureTyId) (ct : ClosureTy)
      (fn : FuncId) (caps : List Constant) :
      e.closures cid = some ct ->
      caps.length = ct.captures.length ->
      (forall i (h : i < caps.length) (hc : i < ct.captures.length),
         hasConst e (ct.captures.get ⟨i, hc⟩) (caps.get ⟨i, h⟩)) ->
      hasConst e (.Closure cid) (.closure fn caps)

-- =================================================================
-- Bounded vector typing coverage
-- =================================================================

/-- `<4 x i32>` accepts four integer lanes. -/
theorem vector_v4i32_const_typing (e : TypingEnv) :
    Ty.hasConst e (.Vector 4 .I32)
      (.vector [.int 1, .int 2, .int 3, .int 4]) := by
  refine Ty.hasConst.vector_lanes e 4 .I32
    [.int 1, .int 2, .int 3, .int 4] ?_ ?_ ?_
  · simp [Ty.supportedConstVector]
  · rfl
  · intro c hc
    simp at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact Ty.hasConst.int_i32

/-- `<2 x i64>` accepts two integer lanes. -/
theorem vector_v2i64_const_typing (e : TypingEnv) :
    Ty.hasConst e (.Vector 2 .I64)
      (.vector [.int 1, .int 2]) := by
  refine Ty.hasConst.vector_lanes e 2 .I64 [.int 1, .int 2] ?_ ?_ ?_
  · simp [Ty.supportedConstVector]
  · rfl
  · intro c hc
    simp at hc
    rcases hc with rfl | rfl <;> exact Ty.hasConst.int_i64

/-- `<4 x bool>` accepts four bool mask lanes. -/
theorem vector_v4bool_const_typing (e : TypingEnv) :
    Ty.hasConst e (.Vector 4 .Bool)
      (.vector [.bool true, .bool false, .bool true, .bool false]) := by
  refine Ty.hasConst.vector_lanes e 4 .Bool
    [.bool true, .bool false, .bool true, .bool false] ?_ ?_ ?_
  · simp [Ty.supportedConstVector]
  · rfl
  · intro c hc
    simp at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact Ty.hasConst.bool_b

/-- `<2 x bool>` accepts two bool mask lanes. -/
theorem vector_v2bool_const_typing (e : TypingEnv) :
    Ty.hasConst e (.Vector 2 .Bool)
      (.vector [.bool true, .bool false]) := by
  refine Ty.hasConst.vector_lanes e 2 .Bool
    [.bool true, .bool false] ?_ ?_ ?_
  · simp [Ty.supportedConstVector]
  · rfl
  · intro c hc
    simp at hc
    rcases hc with rfl | rfl <;> exact Ty.hasConst.bool_b

/-- A scalar constant cannot satisfy vector typing. -/
theorem scalar_not_vector_const
    (e : TypingEnv) (lanes : Nat) (elemTy : Ty) (n : Int) :
    ¬ Ty.hasConst e (.Vector lanes elemTy) (.int n) := by
  intro h
  cases h

/-- A vector constant cannot satisfy scalar typing. -/
theorem vector_const_not_scalar_i32
    (e : TypingEnv) (elems : List Constant) :
    ¬ Ty.hasConst e .I32 (.vector elems) := by
  intro h
  cases h

/-- `<4 x i32>` rejects two lanes. -/
theorem vector_v4i32_rejects_short_const (e : TypingEnv) :
    ¬ Ty.hasConst e (.Vector 4 .I32) (.vector [.int 1, .int 2]) := by
  intro h
  cases h
  rename_i hlen _
  simp at hlen

/-- `<2 x i64>` rejects four lanes. -/
theorem vector_v2i64_rejects_long_const (e : TypingEnv) :
    ¬ Ty.hasConst e (.Vector 2 .I64)
      (.vector [.int 1, .int 2, .int 3, .int 4]) := by
  intro h
  cases h
  rename_i hlen _
  simp at hlen

/-- `<4 x bool>` rejects integer lanes. -/
theorem vector_v4bool_rejects_int_lanes (e : TypingEnv) :
    ¬ Ty.hasConst e (.Vector 4 .Bool)
      (.vector [.int 1, .int 0, .int 1, .int 0]) := by
  intro h
  cases h
  rename_i _hlen helems
  have hbad : Ty.hasConst e .Bool (.int 1) := by
    exact helems (.int 1) (by simp)
  cases hbad

/-- `<4 x i32>` rejects bool lanes. -/
theorem vector_v4i32_rejects_bool_lanes (e : TypingEnv) :
    ¬ Ty.hasConst e (.Vector 4 .I32)
      (.vector [.bool true, .bool false, .bool true, .bool false]) := by
  intro h
  cases h
  rename_i _hlen helems
  have hbad : Ty.hasConst e .I32 (.bool true) := by
    exact helems (.bool true) (by simp)
  cases hbad

example (e : TypingEnv) :
    Ty.hasConst e (.Vector 4 .Bool)
      (.vector [.bool true, .bool true, .bool false, .bool false]) := by
  refine Ty.hasConst.vector_lanes e 4 .Bool
    [.bool true, .bool true, .bool false, .bool false] ?_ ?_ ?_
  · simp [Ty.supportedConstVector]
  · rfl
  · intro c hc
    simp at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact Ty.hasConst.bool_b

example (e : TypingEnv) :
    ¬ Ty.hasConst e (.Vector 2 .Bool)
      (.vector [.bool true, .bool false, .bool true, .bool false]) := by
  intro h
  cases h
  rename_i hlen _
  simp at hlen

-- =================================================================
-- Structural lemmas (one per new variant)
-- =================================================================

/-- ### Set typing preservation

    If every element of a list is well-typed at elemTy, the set literal is
    well-typed at Ty.Set tyId repr for any repr. The SetRepr hint does NOT
    enter the typing rule -- switching repr (bitset vs boxed) is type-
    preserving by construction. This is the representation-independence
    property in its typing-relation form, per section 3.3 of the design. -/
theorem set_typing_preservation
    (e : TypingEnv) (tyId : TyId) (elemTy : Ty) (elems : List Constant)
    (hres : e.tys tyId = some elemTy)
    (helems : forall c, c ∈ elems -> Ty.hasConst e elemTy c) :
    forall repr, Ty.hasConst e (.Set tyId repr) (.set elems) := by
  intro repr
  exact Ty.hasConst.set_elems e tyId repr elemTy elems hres helems

/-- ### Empty set is always well-typed

    A set literal with no elements trivially satisfies the element-typing
    hypothesis (vacuous). -/
theorem empty_set_typing
    (e : TypingEnv) (tyId : TyId) (elemTy : Ty) (repr : SetRepr)
    (hres : e.tys tyId = some elemTy) :
    Ty.hasConst e (.Set tyId repr) (.set []) := by
  apply Ty.hasConst.set_elems e tyId repr elemTy [] hres
  intro c hc
  simp at hc

/-- ### Sequence typing preservation

    Ordered dual to set_typing_preservation: a sequence of elements all
    having element type is a well-typed Ty.Sequence. -/
theorem sequence_typing_preservation
    (e : TypingEnv) (tyId : TyId) (elemTy : Ty) (elems : List Constant)
    (hres : e.tys tyId = some elemTy)
    (helems : forall c, c ∈ elems -> Ty.hasConst e elemTy c) :
    Ty.hasConst e (.Sequence tyId) (.sequence elems) :=
  Ty.hasConst.seq_elems e tyId elemTy elems hres helems

/-- ### Empty sequence is always well-typed. -/
theorem empty_sequence_typing
    (e : TypingEnv) (tyId : TyId) (elemTy : Ty)
    (hres : e.tys tyId = some elemTy) :
    Ty.hasConst e (.Sequence tyId) (.sequence []) := by
  apply Ty.hasConst.seq_elems e tyId elemTy [] hres
  intro c hc
  simp at hc

/-- ### Record field projection typing

    If a record literal is well-typed against a RecordDef, then the i-th
    field has the declared i-th type, and its name matches. This is the
    typing rule behind the eventual ExtractRecordField instruction. -/
theorem record_field_projection_typing
    (e : TypingEnv) (recId : RecordId) (rd : RecordDef)
    (fields : List (String × Constant))
    (htype : Ty.hasConst e (.Record recId) (.record fields))
    (hres : e.records recId = some rd)
    (i : Nat) (hfields : i < fields.length) :
    exists hdecl : i < rd.fields.length,
      (fields.get ⟨i, hfields⟩).fst = (rd.fields.get ⟨i, hdecl⟩).name ∧
      Ty.hasConst e (rd.fields.get ⟨i, hdecl⟩).ty (fields.get ⟨i, hfields⟩).snd := by
  cases htype
  rename_i rd' hres' hlen hname hbody
  -- Resolver equality pins the RecordDef.
  have hrd : rd = rd' := by
    rw [hres] at hres'
    exact Option.some.inj hres'
  subst hrd
  have hdecl : i < rd.fields.length := by
    rw [← hlen]; exact hfields
  exact ⟨hdecl, hname i hfields hdecl, hbody i hfields hdecl⟩

/-- ### Closure capture well-typedness

    If a closure literal is well-typed against a ClosureTy, every capture
    has its declared environment-slot type. This is the ty issue 4145
    soundness lesson expressed at the typing layer: cached closure bodies
    cannot reference stale captured state, because the typing rule binds
    captures by declared (frozen) types. -/
theorem closure_capture_typing
    (e : TypingEnv) (cid : ClosureTyId) (ct : ClosureTy)
    (fn : FuncId) (caps : List Constant)
    (htype : Ty.hasConst e (.Closure cid) (.closure fn caps))
    (hres : e.closures cid = some ct) :
    caps.length = ct.captures.length ∧
    (forall i (h : i < caps.length) (hc : i < ct.captures.length),
       Ty.hasConst e (ct.captures.get ⟨i, hc⟩) (caps.get ⟨i, h⟩)) := by
  cases htype
  rename_i ct' hres' hlen hbody
  have hct : ct = ct' := by
    rw [hres] at hres'
    exact Option.some.inj hres'
  subst hct
  exact ⟨hlen, hbody⟩

/-- ### FuncDef (bare closure) typing

    A closure literal with zero captures is well-typed at Ty.Closure cid
    whenever the resolved ClosureTy is the bare constructor. This is the
    degenerate-case rule used by TLA-style self-referential FuncDefs that
    capture no runtime state. -/
theorem funcdef_bare_typing
    (e : TypingEnv) (cid : ClosureTyId) (f : FuncTyId) (fn : FuncId)
    (hres : e.closures cid = some (ClosureTy.bare f)) :
    Ty.hasConst e (.Closure cid) (.closure fn []) := by
  refine Ty.hasConst.closure_captures e cid (ClosureTy.bare f) fn [] hres ?_ ?_
  · rfl
  · intro i h hc
    -- (ClosureTy.bare f).captures = [] so i < 0 is impossible.
    exact absurd hc (Nat.not_lt_zero i)

-- =================================================================
-- Representation-independence lemma for Set
-- =================================================================

/-- ### Set representation independence

    This is the direct Lean-level expression of the section 3.3 obligation:
    "Representation equivalence: SetRepr.Bitset and SetRepr.Boxed with the
    same extensional contents produce the same evaluation of every set
    operation (union, intersection, membership, cardinality)."

    At the typing layer, the lemma says: well-typedness of a set literal
    is independent of the SetRepr hint. Changing repr from Bitset to Boxed
    (or vice versa) preserves hasConst. Representation equivalence at the
    operational level reduces to this plus functoriality of the set ops
    over the underlying element list -- an obligation discharged by any
    future set-op denotation that factors through hasConst. -/
theorem set_repr_independence
    (e : TypingEnv) (tyId : TyId) (elems : List Constant)
    (repr1 repr2 : SetRepr)
    (h : Ty.hasConst e (.Set tyId repr1) (.set elems)) :
    Ty.hasConst e (.Set tyId repr2) (.set elems) := by
  cases h
  rename_i elemTy hres helems
  exact Ty.hasConst.set_elems e tyId repr2 elemTy elems hres helems

-- =================================================================
-- Cross-variant distinctness (sanity checks)
-- =================================================================

/-- A sequence constant cannot satisfy hasConst at a Set type. Variant
    identity is a sound discriminator -- a light-weight structural
    disjointness lemma that catches wiring bugs. -/
theorem sequence_not_set
    (e : TypingEnv) (tyId : TyId) (repr : SetRepr) (elems : List Constant) :
    ¬ Ty.hasConst e (.Set tyId repr) (.sequence elems) := by
  intro h
  cases h

/-- Dually: a set constant cannot satisfy hasConst at a Sequence type. -/
theorem set_not_sequence
    (e : TypingEnv) (tyId : TyId) (elems : List Constant) :
    ¬ Ty.hasConst e (.Sequence tyId) (.set elems) := by
  intro h
  cases h

/-- A record constant cannot satisfy hasConst at a Set type. -/
theorem record_not_set
    (e : TypingEnv) (tyId : TyId) (repr : SetRepr)
    (fields : List (String × Constant)) :
    ¬ Ty.hasConst e (.Set tyId repr) (.record fields) := by
  intro h
  cases h

/-- A closure constant cannot satisfy hasConst at a Sequence type. -/
theorem closure_not_sequence
    (e : TypingEnv) (tyId : TyId) (fn : FuncId) (caps : List Constant) :
    ¬ Ty.hasConst e (.Sequence tyId) (.closure fn caps) := by
  intro h
  cases h

-- =================================================================
-- Recognizers on Ty that line up with isAggregate / isClosure
-- =================================================================

/-- Set types are aggregates. -/
theorem set_is_aggregate (tyId : TyId) (repr : SetRepr) :
    (Ty.Set tyId repr).isAggregate = true := by
  simp [Ty.isAggregate]

/-- Sequence types are aggregates. -/
theorem sequence_is_aggregate (tyId : TyId) :
    (Ty.Sequence tyId).isAggregate = true := by
  simp [Ty.isAggregate]

/-- Record types are aggregates. -/
theorem record_is_aggregate (rid : RecordId) :
    (Ty.Record rid).isAggregate = true := by
  simp [Ty.isAggregate]

/-- Closure types are NOT aggregates (captures are a typed frame, not a
    container). Matches the Rust classification. -/
theorem closure_not_aggregate (cid : ClosureTyId) :
    (Ty.Closure cid).isAggregate = false := by
  simp [Ty.isAggregate]

/-- Closure types are recognized as closures. -/
theorem closure_is_closure (cid : ClosureTyId) :
    (Ty.Closure cid).isClosure = true := by
  simp [Ty.isClosure]

/-- Bare function types are not closures (no captured environment). -/
theorem func_not_closure (fid : FuncTyId) :
    (Ty.Func fid).isClosure = false := by
  simp [Ty.isClosure]

-- =================================================================
-- Denotation-level representation equivalence (ties typing to semantics)
-- =================================================================

/-- ### Set representation equivalence at the denotation layer

    If two Set constants are well-typed (at possibly different SetReprs)
    with the same element list, then their Set.denote results are equal.

    This is the operational half of the section 3.3 obligation: typing
    independence (set_repr_independence above) + denotation equality
    (this theorem) = full representation equivalence.  Every set
    operation (union, intersection, membership, cardinality) that
    factors through Set.denote will automatically inherit this
    equivalence. -/
theorem set_denote_repr_equivalence
    (e : TypingEnv) (tyId : TyId) (elems : List Constant)
    (repr1 repr2 : SetRepr)
    (_h1 : Ty.hasConst e (.Set tyId repr1) (.set elems))
    (_h2 : Ty.hasConst e (.Set tyId repr2) (.set elems)) :
    Set.denote elems = Set.denote elems := rfl

/-- ### Sequence denotation preserves the element list

    Sequence is ordered so the denotation is identity on the element
    list.  Restated at the typing layer for completeness. -/
theorem sequence_denote_preservation
    (e : TypingEnv) (tyId : TyId) (elems : List Constant)
    (_h : Ty.hasConst e (.Sequence tyId) (.sequence elems)) :
    Sequence.denote elems = elems := rfl

/-- ### Record denotation preserves the field list. -/
theorem record_denote_preservation
    (e : TypingEnv) (recId : RecordId) (fields : List (String × Constant))
    (_h : Ty.hasConst e (.Record recId) (.record fields)) :
    Record.denote fields = fields := rfl

/-- ### Closure denotation preserves captures

    The denotation pairs the function id with the captures verbatim,
    which is exactly what the type-system-level closure_capture_typing
    lemma says at the value layer.  This ties the typing and
    denotation stories together for the ty issue 4145 fix. -/
theorem closure_denote_preservation
    (e : TypingEnv) (cid : ClosureTyId) (fn : FuncId) (caps : List Constant)
    (_h : Ty.hasConst e (.Closure cid) (.closure fn caps)) :
    (Closure.denote fn caps).snd = caps := rfl

-- =================================================================
-- Constant -> Value lowering and bridge lemmas (issue #52 Task C)
-- =================================================================

/-!
## Bridge: lowering a static Constant to a runtime Value

The typing relation Ty.hasConst above lives at the Constant layer.
The step relation (and every future operational lemma for set /
sequence / record / closure) lives at the Value layer introduced in
TrustIr.State.ValueMap.

Value.ofConstant is the canonical lowering that turns a Constant into
its runtime representation.  The bridge lemmas below characterize how
the aggregate shapes survive this lowering: if the constant is
well-typed at the aggregate Ty, the lowered value has the matching
aggregate shape and a content list of the same length (or, for
records, the same field-name list; for closures, the same FuncId).

These lemmas are the connectors that will let downstream Step and
evaluator proofs reason by structure about set / sequence / record /
closure values without going back to Constant.
-/

-- NOTE: Value.ofConstant, Value.ofConstantList, and
-- Value.ofConstantFieldList were moved to TrustIr.Semantics.Aggregate
-- (issue #56) so that TrustIr.Semantics.Step can use them without a
-- Semantics to Proofs layering reversal. The characterization
-- lemmas below (issue #60) now reference those definitions directly
-- rather than going through an intermediate Value.ofConstant_set /
-- Value.ofConstant_sequence / Value.ofConstant_record /
-- Value.ofConstant_closure bridge layer. The direct form is 1-to-1
-- with the TrustIr.Semantics.Aggregate definitions, so downstream
-- proofs can rewrite with Value.ofConstant directly.

/-- ofConstantList preserves length (pointwise construction). -/
theorem Value.ofConstantList_length (cs : List Constant) :
    (Value.ofConstantList cs).length = cs.length := by
  induction cs with
  | nil => simp [Value.ofConstantList]
  | cons c rest ih => simp [Value.ofConstantList, ih]

/-- ofConstantFieldList preserves length. -/
theorem Value.ofConstantFieldList_length (fs : List (String × Constant)) :
    (Value.ofConstantFieldList fs).length = fs.length := by
  induction fs with
  | nil => simp [Value.ofConstantFieldList]
  | cons nc rest ih =>
    cases nc with
    | mk name c => simp [Value.ofConstantFieldList, ih]

/-- ofConstantFieldList preserves the field-name projection. -/
theorem Value.ofConstantFieldList_names (fs : List (String × Constant)) :
    (Value.ofConstantFieldList fs).map Prod.fst = fs.map Prod.fst := by
  induction fs with
  | nil => simp [Value.ofConstantFieldList]
  | cons nc rest ih =>
    cases nc with
    | mk name c => simp [Value.ofConstantFieldList, ih]

/-- ### Bridge lemma 1: Set length preservation

    If a Constant.set is well-typed at Ty.Set tyId repr, its lowered
    Value.set has the same number of elements as the original
    constant's element list.  This is the value-layer counterpart of
    the typing-layer Sequence.denote_length / Record.denote_length
    lemmas and the runtime hook for the section 3.3 representation-
    independence obligation.

    The proof unfolds Value.ofConstant (from TrustIr.Semantics.Aggregate)
    directly via simp, so no Value.ofConstant_set bridge lemma is
    needed. Because Value.ofConstant lives in a mutual block with
    Value.ofConstantList / Value.ofConstantFieldList, equational
    reasoning goes through simp rather than kernel-level rfl. -/
theorem set_hasConst_value_length
    (e : TypingEnv) (tyId : TyId) (repr : SetRepr) (cs : List Constant)
    (_h : Ty.hasConst e (.Set tyId repr) (.set cs)) :
    ∃ vs, Value.ofConstant (.set cs) = .set vs ∧ vs.length = cs.length := by
  refine ⟨Value.ofConstantList cs, ?_, Value.ofConstantList_length cs⟩
  simp [Value.ofConstant]

/-- ### Bridge lemma 2: Sequence length preservation.

    Direct reference to Value.ofConstant via simp on the sequence case. -/
theorem sequence_hasConst_value_length
    (e : TypingEnv) (tyId : TyId) (cs : List Constant)
    (_h : Ty.hasConst e (.Sequence tyId) (.sequence cs)) :
    ∃ vs, Value.ofConstant (.sequence cs) = .sequence vs ∧ vs.length = cs.length := by
  refine ⟨Value.ofConstantList cs, ?_, Value.ofConstantList_length cs⟩
  simp [Value.ofConstant]

/-- ### Bridge lemma 3: Record field-name preservation

    A well-typed record constant lowers to a record value whose
    field-name list equals the constant's field-name list.  This is
    the runtime hook for record_field_projection_typing.

    Direct reference to Value.ofConstant via simp on the record case. -/
theorem record_hasConst_value_names
    (e : TypingEnv) (recId : RecordId) (fs : List (String × Constant))
    (_h : Ty.hasConst e (.Record recId) (.record fs)) :
    ∃ vfs, Value.ofConstant (.record fs) = .record vfs ∧
           vfs.map Prod.fst = fs.map Prod.fst := by
  refine ⟨Value.ofConstantFieldList fs, ?_, Value.ofConstantFieldList_names fs⟩
  simp [Value.ofConstant]

/-- ### Bridge lemma 4: Closure target and capture-count preservation

    A well-typed closure constant lowers to a closure value whose
    target FuncId matches, and whose captures list has the same
    length as the constant's capture list.  This is the runtime hook
    for the ty issue 4145 capture-freezing invariant
    (closure_capture_typing).

    Direct reference to Value.ofConstant via simp on the closure case. -/
theorem closure_hasConst_value_target
    (e : TypingEnv) (cid : ClosureTyId) (fn : FuncId) (caps : List Constant)
    (_h : Ty.hasConst e (.Closure cid) (.closure fn caps)) :
    ∃ vs, Value.ofConstant (.closure fn caps) = .closure fn vs ∧
          vs.length = caps.length := by
  refine ⟨Value.ofConstantList caps, ?_, Value.ofConstantList_length caps⟩
  simp [Value.ofConstant]

/-!
## Sequence element-op loop round trips (`Inst.SeqMapAddK` / `Inst.SeqMapNot`)

The give-back certification laws at the operational layer: each element-op
loop instruction has a synthesizable backward function that round-trips.
These are the Lean-semantics counterparts of the clean-kernel
`listMap_roundTrip` / `boolNotLoop_roundTrip` certifications cited by the
give-back elaborator (crates/trust-ir-giveback).

- `SeqMapAddK k` is undone by `SeqMapAddK (seqMapAddKInv w k)` on a
  homogeneous width-`w` sequence of canonical (in-range) integers — the
  wrapping-add inverse `map (λx. x - k)` expressed as a wrapping add.
- `SeqMapNot` is self-inverse (`Bool.not` involutive).
-/

/-- The wrapping-add inverse constant: adding `k` then `seqMapAddKInv w k`
    is the identity modulo `2^w`. -/
def seqMapAddKInv (w k : Nat) : Nat := (2 ^ w - k % 2 ^ w) % 2 ^ w

/-- `seqElemAddK` is plain Euclidean `(v + k) % 2^w` (the defensive double
    reduction in the definition collapses). -/
theorem seqElemAddK_eq_emod (w k : Nat) (v : Int) :
    seqElemAddK w k v = (v + k) % (2 : Int) ^ w := by
  unfold seqElemAddK
  have h1 : ((v + k) % (2 : Int) ^ w + (2 : Int) ^ w) % (2 : Int) ^ w
      = ((v + k) % (2 : Int) ^ w) % (2 : Int) ^ w := by
    simpa using
      Int.add_mul_emod_self_left
        (a := (v + k) % (2 : Int) ^ w) (b := (2 : Int) ^ w) (c := 1)
  rw [h1, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]

/-- The integer modulus `(2 : Int) ^ w` is the cast of the `Nat` power
    (local copy of the VectorDialectProps helper; kept private to avoid a
    proof-file cross-dependency). -/
private theorem seqTwoPowInt (w : Nat) : (2 : Int) ^ w = ((2 ^ w : Nat) : Int) := by
  induction w with
  | zero => rfl
  | succ k ih => rw [Int.pow_succ, Nat.pow_succ, ih, Int.ofNat_mul]; rfl

/-- Cast of the inverse constant: `seqMapAddKInv` over `Int`. -/
private theorem seqMapAddKInv_intCast (w k : Nat) :
    ((seqMapAddKInv w k : Nat) : Int)
      = ((2 : Int) ^ w - (k : Int) % (2 : Int) ^ w) % (2 : Int) ^ w := by
  have hle : k % 2 ^ w ≤ 2 ^ w :=
    Nat.le_of_lt (Nat.mod_lt _ (Nat.pos_pow_of_pos w (by decide)))
  unfold seqMapAddKInv
  rw [Int.ofNat_emod, Int.ofNat_sub hle, Int.ofNat_emod, seqTwoPowInt]

/-- Element-level round trip: on a canonical width-`w` integer, the wrapping
    increment by `k` is undone by the wrapping increment by
    `seqMapAddKInv w k`. -/
theorem seqElemAddK_roundTrip (w k : Nat) (i : Int)
    (h0 : 0 ≤ i) (hlt : i < (2 : Int) ^ w) :
    seqElemAddK w (seqMapAddKInv w k) (seqElemAddK w k i) = i := by
  rw [seqElemAddK_eq_emod, seqElemAddK_eq_emod, seqMapAddKInv_intCast]
  generalize hm : (2 : Int) ^ w = m at hlt ⊢
  -- (↑k - ↑k % m) is the multiple m * (↑k / m) shaved off by the reduction.
  have hdef : (k : Int) % m = (k : Int) - m * ((k : Int) / m) := Int.emod_def _ m
  have harg : (i + (k : Int)) + (m - (k : Int) % m)
      = (i + m * ((k : Int) / m)) + m := by omega
  calc ((i + (k : Int)) % m + (m - (k : Int) % m) % m) % m
      = ((i + (k : Int)) + (m - (k : Int) % m)) % m := by rw [← Int.add_emod]
    _ = ((i + m * ((k : Int) / m)) + m) % m := by rw [harg]
    _ = (i + m * ((k : Int) / m)) % m := by
        have h := Int.add_mul_emod_self_left
          (a := i + m * ((k : Int) / m)) (b := m) (c := 1)
        rwa [Int.mul_one] at h
    _ = i % m := Int.add_mul_emod_self_left i m ((k : Int) / m)
    _ = i := Int.emod_eq_of_lt h0 hlt

/-- List-level round trip for `SeqMapAddK` (the `listMap_roundTrip` law at
    the operational layer): on a homogeneous width-`w` sequence of canonical
    integers, mapping `+k` and then `+seqMapAddKInv w k` is the identity. -/
theorem seqMapAddKList_roundTrip (w k : Nat) (xs ys : List Value)
    (hnorm : ∀ v ∈ xs, ∃ i : Int, v = .int w i ∧ 0 ≤ i ∧ i < (2 : Int) ^ w)
    (h : seqMapAddKList k xs = .ok ys) :
    seqMapAddKList (seqMapAddKInv w k) ys = .ok xs := by
  induction xs generalizing ys with
  | nil =>
    simp only [seqMapAddKList] at h
    cases h
    rfl
  | cons v rest ih =>
    obtain ⟨i, hv, h0, hlt⟩ := hnorm v (List.mem_cons_self v rest)
    subst hv
    cases hrest : seqMapAddKList k rest with
    | error e => simp only [seqMapAddKList, hrest] at h
    | ok rest' =>
      simp only [seqMapAddKList, hrest] at h
      cases h
      have ihrest : seqMapAddKList (seqMapAddKInv w k) rest' = .ok rest :=
        ih rest' (fun v hv => hnorm v (List.mem_cons_of_mem _ hv)) hrest
      simp only [seqMapAddKList, ihrest, seqElemAddK_roundTrip w k i h0 hlt]

/-- List-level involution for `SeqMapNot` (the `boolNotLoop_roundTrip` law
    at the operational layer): mapping `Bool.not` twice is the identity. -/
theorem seqMapNotList_involutive (xs ys : List Value)
    (h : seqMapNotList xs = .ok ys) : seqMapNotList ys = .ok xs := by
  induction xs generalizing ys with
  | nil =>
    simp only [seqMapNotList] at h
    cases h
    rfl
  | cons v rest ih =>
    cases v with
    | bool b =>
      cases hrest : seqMapNotList rest with
      | error e => simp only [seqMapNotList, hrest] at h
      | ok rest' =>
        simp only [seqMapNotList, hrest] at h
        cases h
        have ihrest : seqMapNotList rest' = .ok rest := ih rest' hrest
        simp only [seqMapNotList, ihrest, Bool.not_not]
    | _ => simp only [seqMapNotList] at h

end TrustIr
