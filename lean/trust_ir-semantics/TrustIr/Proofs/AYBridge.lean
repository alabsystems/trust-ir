-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Phase 5 ay bridge: reflection layer connecting Lean proofs to ay SMT
-- automated proofs via a shared expression language.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 5
-- Reference: de Moura & Bjorner, "Z3: An Efficient SMT Solver", TACAS 2008
-- Reference: Ebner et al., "A Metaprogramming Framework for Formal Verification",
--            Proc. ACM Program. Lang. (ICFP), 2017

import TrustIr.Semantics.Eval

namespace TrustIr

/-!
# ay Bridge (Phase 5)

This module defines the reflection layer that bridges Lean-checked proofs
with ay (SMT solver) automated proofs.

## Architecture

The bridge has three layers:

1. **TrustIrExpr** -- an inductive type mirroring ay SMT-LIB expressions,
   restricted to the bitvector and boolean theories used by TrustIr.

2. **Encoding** -- functions that translate TrustIr instruction operands
   into TrustIrExpr, so ay can reason about instruction behavior.

3. **Reflection** -- an interpretation function from TrustIrExpr back to
   Lean Prop, plus a soundness axiom: if ay reports UNSAT, the
   corresponding Lean Prop holds.

## Trust model

The ay solver is an EXTERNAL ORACLE. We do NOT verify ay's internals.
Instead, we trust a single axiom (ay_sound): if ay says UNSAT for a
formula, that formula is indeed unsatisfiable. This is the standard
"proof-producing solver" trust model used by Isabelle/HOL's smt method
and Coq's SMTCoq.

In production, ay can optionally produce proof certificates that are
independently checked. The axiom here is the minimal trust assumption
needed to USE ay results in Lean proofs.

## Intended usage by TrustCg (framework — awaiting instantiation)

This module is a proof *framework*: the theorems below are proved, but
`ay_check` is an uninstantiated `opaque` (no `@[extern]`/`@[implemented_by]`
binding, no SMT-LIB printer, no certificate importer — see "Future Work").
Until it is instantiated, no `ay_check e = .unsat` fact can be produced inside
Lean, so nothing is cross-verified through *this* bridge yet. (The Rust
`trust-ir-ay` adapter performs solver-backed checks on a parallel, Lean-
disconnected path; it does not instantiate `ay_check`.)

When instantiated, TrustCg would verify optimization passes by:
1. Encoding the original and optimized instruction as `TrustIrExpr`,
2. asserting their inequality and sending it to ay,
3. concluding equivalence if ay returns UNSAT,
4. and lifting that to a Lean proof via the `ay_sound_unsat` axiom.
-/

-- =================================================================
-- SMT expression type
-- =================================================================

/-- SMT expression type mirroring ay bitvector and boolean theories.
    This is the shared language between Lean and ay. -/
inductive TrustIrExpr where
  -- Bitvector constants and operations
  | bvConst  : (width : Nat) -> Int -> TrustIrExpr
  | bvAdd    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSub    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvMul    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvUDiv   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSDiv   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvURem   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSRem   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvAnd    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvOr     : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvXor    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvNeg    : TrustIrExpr -> TrustIrExpr
  | bvNot    : TrustIrExpr -> TrustIrExpr
  | bvShl    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvLShr   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvAShr   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  -- Boolean operations
  | boolConst : Bool -> TrustIrExpr
  | boolNot   : TrustIrExpr -> TrustIrExpr
  | boolAnd   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | boolOr    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | boolImpl  : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  -- Comparisons (bitvector -> bool)
  | eq       : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvUlt    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvUle    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSlt    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSle    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  -- Control
  | ite      : TrustIrExpr -> TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  -- Variables (for universally quantified formulas)
  | var      : String -> Nat -> TrustIrExpr
  deriving Repr

-- =================================================================
-- Denotational semantics for TrustIrExpr
-- =================================================================

/-- Environment: maps variable names to integer values. -/
def SMTEnv := String -> Int

/-- Default environment: all variables are 0. -/
def SMTEnv.default : SMTEnv := fun _ => 0

/-- Truncate an integer to width bits (unsigned modular arithmetic). -/
private def truncBV (val : Int) (width : Nat) : Int :=
  let modulus := (2 : Int) ^ width
  ((val % modulus) + modulus) % modulus

/-- Interpret a width-bit bitvector as a two's-complement SIGNED integer.
    SMT-LIB `bvslt`/`bvsle`/`bvsdiv`/`bvsrem`/`bvashr` are signed operations;
    evaluating them on the raw unsigned residue (as the old code did, making
    them textually identical to their unsigned counterparts) is unsound. -/
private def toSignedBV (val : Int) (width : Nat) : Int :=
  let u := truncBV val width
  let half := (2 : Int) ^ (width - 1)
  if u ≥ half then u - (2 : Int) ^ width else u

/-- Evaluate a TrustIrExpr to an Int given an environment and a bitvector width.
    Bitvector operations use modular arithmetic at the specified width.
    The width parameter allows cross-target evaluation (e.g., 32-bit for
    i32 operations, 64-bit for i64). Defaults to 64 for backward
    compatibility.
    Boolean operations map true -> 1, false -> 0. -/
def TrustIrExpr.evalAt (env : SMTEnv) (w : Nat) : TrustIrExpr -> Int
  | .bvConst width val  => truncBV val width
  | .bvAdd e1 e2        => truncBV (e1.evalAt env w + e2.evalAt env w) w
  | .bvSub e1 e2        => truncBV (e1.evalAt env w - e2.evalAt env w) w
  | .bvMul e1 e2        => truncBV (e1.evalAt env w * e2.evalAt env w) w
  | .bvUDiv e1 e2       =>
    let d := e2.evalAt env w
    if d == 0 then 0 else truncBV (e1.evalAt env w / d) w
  | .bvSDiv e1 e2       =>
    let d := toSignedBV (e2.evalAt env w) w
    -- SMT-LIB `bvsdiv` rounds the quotient toward zero: `Int.div` (T-rounding),
    -- not the Euclidean `/` operator. `Int.div (-7) 2 = -3` matches bvsdiv;
    -- ediv would give -4.
    if d == 0 then 0 else truncBV (Int.div (toSignedBV (e1.evalAt env w) w) d) w
  | .bvURem e1 e2       =>
    let d := e2.evalAt env w
    if d == 0 then 0 else truncBV (e1.evalAt env w % d) w
  | .bvSRem e1 e2       =>
    let d := toSignedBV (e2.evalAt env w) w
    -- SMT-LIB `bvsrem` takes the sign of the dividend: `Int.mod` (T-rounding),
    -- not the Euclidean `%` operator. `Int.mod (-7) 3 = -1` matches bvsrem;
    -- emod would give 2.
    if d == 0 then 0 else truncBV (Int.mod (toSignedBV (e1.evalAt env w) w) d) w
  | .bvAnd e1 e2        => Int.land (e1.evalAt env w) (e2.evalAt env w)
  | .bvOr e1 e2         => Int.lor (e1.evalAt env w) (e2.evalAt env w)
  | .bvXor e1 e2        => Int.xor (e1.evalAt env w) (e2.evalAt env w)
  | .bvNeg e             => truncBV (-(e.evalAt env w)) w
  | .bvNot e             => Int.xor (e.evalAt env w) ((2 : Int) ^ w - 1)
  | .bvShl e1 e2        => truncBV ((e1.evalAt env w) * ((2 : Int) ^ (e2.evalAt env w).toNat)) w
  | .bvLShr e1 e2       => truncBV ((e1.evalAt env w) / ((2 : Int) ^ (e2.evalAt env w).toNat)) w
  | .bvAShr e1 e2       => truncBV (Int.fdiv (toSignedBV (e1.evalAt env w) w) ((2 : Int) ^ (e2.evalAt env w).toNat)) w
  | .boolConst b         => if b then 1 else 0
  | .boolNot e           => if e.evalAt env w == 0 then 1 else 0
  | .boolAnd e1 e2      => if e1.evalAt env w != 0 && e2.evalAt env w != 0 then 1 else 0
  | .boolOr e1 e2       => if e1.evalAt env w != 0 || e2.evalAt env w != 0 then 1 else 0
  | .boolImpl e1 e2     => if e1.evalAt env w == 0 || e2.evalAt env w != 0 then 1 else 0
  | .eq e1 e2            => if e1.evalAt env w == e2.evalAt env w then 1 else 0
  | .bvUlt e1 e2        => if e1.evalAt env w < e2.evalAt env w then 1 else 0
  | .bvUle e1 e2        => if e1.evalAt env w <= e2.evalAt env w then 1 else 0
  | .bvSlt e1 e2        => if toSignedBV (e1.evalAt env w) w < toSignedBV (e2.evalAt env w) w then 1 else 0
  | .bvSle e1 e2        => if toSignedBV (e1.evalAt env w) w ≤ toSignedBV (e2.evalAt env w) w then 1 else 0
  | .ite c t e           => if c.evalAt env w != 0 then t.evalAt env w else e.evalAt env w
  | .var name _          => env name

/-- Backward-compatible eval: defaults to 64-bit width. -/
def TrustIrExpr.eval (env : SMTEnv) (expr : TrustIrExpr) : Int :=
  expr.evalAt env 64

-- =================================================================
-- Encoding TrustIr operations as SMT expressions
-- =================================================================

/-- Encode a TrustIr BinOp as a TrustIrExpr combinator.
    Maps each BinOp variant to the corresponding SMT operation. -/
def encodeBinOp (op : BinOp) (lhs rhs : TrustIrExpr) : TrustIrExpr :=
  match op with
  | .Add   => .bvAdd lhs rhs
  | .Sub   => .bvSub lhs rhs
  | .Mul   => .bvMul lhs rhs
  | .UDiv  => .bvUDiv lhs rhs
  | .SDiv  => .bvSDiv lhs rhs
  | .URem  => .bvURem lhs rhs
  | .SRem  => .bvSRem lhs rhs
  | .FAdd  => .bvAdd lhs rhs   -- float ops approximated as BV for now
  | .FSub  => .bvSub lhs rhs
  | .FMul  => .bvMul lhs rhs
  | .FDiv  => .bvUDiv lhs rhs
  | .FRem  => .bvURem lhs rhs
  | .And   => .bvAnd lhs rhs
  | .Or    => .bvOr lhs rhs
  | .Xor   => .bvXor lhs rhs
  | .Shl   => .bvShl lhs rhs
  | .LShr  => .bvLShr lhs rhs
  | .AShr  => .bvAShr lhs rhs
  -- Bool connectives. On the 0/1 carrier the bitwise BV ops agree pointwise with
  -- the logical ones, so this encoding is exact for well-formed Bool operands --
  -- and the SOLVER side, unlike the Clean prelude's opaque `Int.lor`, reasons
  -- about `bvAnd`/`bvOr`/`bvXor` natively.
  | .BAnd  => .bvAnd lhs rhs
  | .BOr   => .bvOr lhs rhs
  | .BXor  => .bvXor lhs rhs

/-- Encode a TrustIr ICmpOp as a TrustIrExpr combinator. -/
def encodeICmp (op : ICmpOp) (lhs rhs : TrustIrExpr) : TrustIrExpr :=
  match op with
  | .Eq  => .eq lhs rhs
  | .Ne  => .boolNot (.eq lhs rhs)
  | .Ult => .bvUlt lhs rhs
  | .Ule => .bvUle lhs rhs
  | .Ugt => .bvUlt rhs lhs
  | .Uge => .bvUle rhs lhs
  | .Slt => .bvSlt lhs rhs
  | .Sle => .bvSle lhs rhs
  | .Sgt => .bvSlt rhs lhs
  | .Sge => .bvSle rhs lhs

-- =================================================================
-- ay oracle interface
-- =================================================================

/-- Result of a ay satisfiability check. -/
inductive AYResult where
  | sat     : AYResult
  | unsat   : AYResult
  | unknown : AYResult
  deriving DecidableEq, Repr

/-- Opaque ay check function. This represents the external call to ay.
    It is intended to be instantiated via FFI or process invocation; it is
    NOT bound today (no `@[extern]`/`@[implemented_by]`), so it is an
    uninstantiated framework hook — no `ay_check e = .unsat` fact can be
    produced inside Lean until that binding (and the SMT-LIB serializer +
    certificate importer in "Future Work") lands. The argument is a
    `TrustIrExpr` representing a formula to check satisfiability of. -/
instance : Inhabited AYResult := Inhabited.mk .unknown

opaque ay_check : TrustIrExpr -> AYResult

-- =================================================================
-- Reflection: TrustIrExpr to Lean Prop
-- =================================================================

/-- Interpret a TrustIrExpr as a Lean Prop.
    A formula is "true" if it evaluates to nonzero for all environments. -/
def TrustIrExpr.toProp (expr : TrustIrExpr) : Prop :=
  forall env : SMTEnv, expr.eval env != 0

/-- A formula is valid if it holds for all environments. -/
def formula_valid (expr : TrustIrExpr) : Prop :=
  TrustIrExpr.toProp expr

/-- A formula is unsatisfiable if no environment makes it true. -/
def formula_unsat (expr : TrustIrExpr) : Prop :=
  forall env : SMTEnv, expr.eval env = 0

-- =================================================================
-- Soundness axiom
-- =================================================================

/-- The ay soundness axiom: if ay reports UNSAT for a formula,
    then the formula is indeed unsatisfiable (no environment satisfies it).

    This is the SOLE trust assumption for the ay bridge. Everything
    else is verified in Lean.

    Trust justification:
    - ay is a mature, extensively tested SMT solver
    - ay supports proof certificate generation for independent checking
    - In production, we can validate ay's certificates with an independent
      checker (reducing trust to the checker, not ay itself) -/
axiom ay_sound_unsat :
  forall (expr : TrustIrExpr),
    ay_check expr = .unsat -> formula_unsat expr

/-- Contrapositive of soundness: if a formula IS satisfiable (some env
    makes it nonzero), then ay does NOT report UNSAT.
    This follows logically from ay_sound_unsat. -/
theorem ay_sound_contrapositive (expr : TrustIrExpr)
    (hSat : exists (env : SMTEnv), expr.eval env ≠ 0) :
    ay_check expr ≠ .unsat := by
  intro hUnsat
  have hAllZero := ay_sound_unsat expr hUnsat
  match hSat with
  | ⟨env, hNonzero⟩ => exact absurd (hAllZero env) hNonzero

-- =================================================================
-- Verification of instruction equivalence via ay
-- =================================================================

/-- Two TrustIrExpr are equivalent if they evaluate to the same value
    in every environment. -/
def expr_equiv (e1 e2 : TrustIrExpr) : Prop :=
  forall env : SMTEnv, e1.eval env = e2.eval env

/-- To check expr_equiv via ay, we check UNSAT of (e1 != e2).
    If ay says UNSAT for (e1 xor e2) -- i.e., they can never differ --
    then e1 and e2 are equivalent. -/
def expr_diff (e1 e2 : TrustIrExpr) : TrustIrExpr :=
  .boolNot (.eq e1 e2)

/-- ay-verified expression equivalence: if ay says the expressions
    can never differ, they are equivalent. -/
theorem ay_expr_equiv (e1 e2 : TrustIrExpr)
    (hUnsat : ay_check (expr_diff e1 e2) = .unsat) :
    expr_equiv e1 e2 := by
  have hAllZero := ay_sound_unsat (expr_diff e1 e2) hUnsat
  intro env
  have hZero := hAllZero env
  -- hZero: (boolNot (eq e1 e2)).eval env = 0
  -- boolNot x evaluates to: if x.evalAt env 64 == 0 then 1 else 0
  -- so hZero = 0 means the else branch was taken, i.e., (eq e1 e2).evalAt env 64 != 0
  -- eq e1 e2 evaluates to: if e1.evalAt env 64 == e2.evalAt env 64 then 1 else 0
  -- so non-zero means e1.evalAt env 64 = e2.evalAt env 64
  simp only [expr_diff, TrustIrExpr.eval, TrustIrExpr.evalAt, formula_unsat] at hZero
  -- hZero now relates to the if-then-else evaluation
  -- Extract: if (eq result) == 0 then 1 else 0 = 0, so (eq result) != 0
  -- i.e., e1.evalAt env 64 == e2.evalAt env 64
  simp only [TrustIrExpr.eval, TrustIrExpr.evalAt, expr_equiv]
  by_cases h : TrustIrExpr.evalAt env 64 e1 = TrustIrExpr.evalAt env 64 e2
  · exact h
  · -- If they differ, boolNot (eq e1 e2) = 1, contradicting hZero
    exfalso
    simp [TrustIrExpr.evalAt, h] at hZero

-- =================================================================
-- Verified constant folding via ay
-- =================================================================

/-- ay-verified constant fold: if ay confirms that a BinOp on two
    constants equals a known result, the fold is sound.

    Usage by TrustCg:
    1. Observe BinOp op (Const w a) (Const w b) in the IR
    2. Compute candidate result r
    3. Ask ay: is (encodeBinOp op (bvConst w a) (bvConst w b)) == (bvConst w r)?
    4. If ay says UNSAT for the negation, apply this theorem -/
theorem ay_constant_fold (op : BinOp) (width : Nat)
    (lhsVal rhsVal result : Int)
    (hAY : ay_check (expr_diff
      (encodeBinOp op (.bvConst width lhsVal) (.bvConst width rhsVal))
      (.bvConst width result)) = .unsat) :
    expr_equiv
      (encodeBinOp op (.bvConst width lhsVal) (.bvConst width rhsVal))
      (.bvConst width result) :=
  ay_expr_equiv _ _ hAY

-- =================================================================
-- Bridge from SMT equivalence to TrustIr inst_equiv
-- =================================================================

/-- Two instructions are TrustIr-equivalent if they produce the same
    result on every machine state. (Same definition as in
    TransformCorrectness.lean, repeated here for self-containedness.) -/
def ay_inst_equiv (i1 i2 : Inst) : Prop :=
  forall s, Sem.run (stepInst i1) s = Sem.run (stepInst i2) s

/-- Faithful encoding relation: an instruction's monadic behavior is
    determined by its SMT encoding, via some state-to-environment map.

    An encoding is faithful for instruction i if: for any other
    instruction i' with encoding encode', whenever encode and encode'
    agree on all stateToEnv-images, the instructions must produce the
    same monadic result on all states.

    In practice, TrustCg instantiates this per optimization pass by
    providing per-instruction encoding correctness lemmas (like
    add_encoding_correct below) that chain together to establish
    this relational condition. The per-instruction case analysis
    (showing TrustIrExpr.eval faithfully models semIntBinOp etc.) is
    the main verification obligation when instantiating the bridge. -/
def encoding_determines_behavior (inst : Inst) (encode : TrustIrExpr)
    (stateToEnv : MachineState -> SMTEnv) : Prop :=
  forall (inst' : Inst) (encode' : TrustIrExpr),
    (forall s, encode.eval (stateToEnv s) = encode'.eval (stateToEnv s)) ->
    forall s, Sem.run (stepInst inst) s = Sem.run (stepInst inst') s

/-- Framework theorem: ay-verified SMT equivalence of instruction
    encodings implies semantic equivalence of the instructions.

    This is the key bridge theorem. It requires:
    1. A faithful encoding of both instructions into TrustIrExpr
    2. A proof that the encodings are equivalent (from ay or otherwise)
    3. A proof that each encoding faithfully determines its instruction's
       behavior via encoding_determines_behavior

    The faithfulness proof (step 3) is instruction-specific and must
    be provided by the caller. We state the framework here; TrustCg
    instantiates it per optimization pass.

    Proof sketch: hFaithful1 says that i1's behavior is determined by
    encode1. hEquiv says encode1 and encode2 agree on all environments,
    and in particular on all stateToEnv images. Instantiating hFaithful1
    with i2 and encode2 yields the conclusion: stepInst i1 and
    stepInst i2 agree on all states. -/
theorem ay_equiv_implies_inst_equiv (i1 i2 : Inst)
    (encode1 encode2 : TrustIrExpr)
    (stateToEnv : MachineState -> SMTEnv)
    (hEquiv : expr_equiv encode1 encode2)
    (hFaithful1 : encoding_determines_behavior i1 encode1 stateToEnv)
    (_hFaithful2 : encoding_determines_behavior i2 encode2 stateToEnv)
    : ay_inst_equiv i1 i2 := by
  -- hFaithful1 says: for any inst' and encode', if encode1 and encode'
  -- agree on all stateToEnv-images, then stepInst i1 = stepInst inst'.
  -- hEquiv says: encode1.eval env = encode2.eval env for all env.
  -- Instantiate hFaithful1 with inst' := i2, encode' := encode2.
  -- The premise requires: encode1.eval (stateToEnv s) = encode2.eval (stateToEnv s)
  -- for all s, which follows from hEquiv.
  intro s
  have hEnvAgree : forall s', encode1.eval (stateToEnv s') = encode2.eval (stateToEnv s') :=
    fun s' => hEquiv (stateToEnv s')
  exact hFaithful1 i2 encode2 hEnvAgree s

-- =================================================================
-- Concrete encoding correctness lemmas
-- =================================================================

/-- Addition encoding is correct: the SMT encoding of Add matches
    the TrustIr semIntBinOp .Add semantics (both are modular addition). -/
theorem add_encoding_correct (width : Nat) (a b : Int) :
    TrustIrExpr.eval SMTEnv.default
      (encodeBinOp .Add (.bvConst width a) (.bvConst width b)) =
    truncBV (truncBV a width + truncBV b width) 64 := by
  simp [encodeBinOp, TrustIrExpr.eval, TrustIrExpr.evalAt]

/-- Width-parameterized addition encoding correctness. -/
theorem add_encoding_correct_at (w width : Nat) (a b : Int) :
    TrustIrExpr.evalAt SMTEnv.default w
      (encodeBinOp .Add (.bvConst width a) (.bvConst width b)) =
    truncBV (truncBV a width + truncBV b width) w := by
  simp [encodeBinOp, TrustIrExpr.evalAt]

/-- Boolean constant encoding: true encodes to 1, false to 0. -/
theorem bool_const_encoding (b : Bool) :
    TrustIrExpr.eval SMTEnv.default (.boolConst b) = if b then 1 else 0 := by
  simp [TrustIrExpr.eval, TrustIrExpr.evalAt]

/-- Equality encoding reflexivity: eq e e always evaluates to 1 (true). -/
theorem eq_refl_encoding (e : TrustIrExpr) (env : SMTEnv) :
    TrustIrExpr.eval env (.eq e e) = 1 := by
  simp [TrustIrExpr.eval, TrustIrExpr.evalAt]

-- =================================================================
-- Future work
-- =================================================================

/-
## Planned extensions

1. **Proof certificate validation:**
   Instead of the ay_sound_unsat axiom, parse ay's proof certificates
   and verify them in Lean. This eliminates trust in ay entirely.
   Reference: Barbosa et al., "Flexible Proof Production in an
   Industrial-Strength SMT Solver", CADE 2023.

2. **Floating-point theory:**
   Extend TrustIrExpr with IEEE 754 floating-point operations (FP theory
   in SMT-LIB). Currently float ops are approximated as bitvectors.

3. **Memory theory:**
   Extend TrustIrExpr with array theory for reasoning about memory
   operations. This enables ay-verified alias analysis.

4. **Quantifier support:**
   Add forall/exists to TrustIrExpr for universally quantified properties
   (e.g., "for all inputs, this optimization is correct").

5. **Incremental solving:**
   Support ay's incremental mode (push/pop) for verifying multiple
   related properties efficiently.

## Instantiating `ay_check` — the precise FFI boundary (audit #86)

`ay_check` is the single uninstantiated hook. Closing it has exactly three
parts, the first two of which are in-repo and the third of which is ay-side:

1. **Serializer (TrustIrExpr → SMT-LIB).** A total `TrustIrExpr.toSmtLib`
   printer that emits a `(check-sat)`-style script. This is pure Lean/Rust and
   can be written and tested in-repo *before* any solver exists. NOTE: the
   signed/shift evaluator divergences in `TrustIrExpr.evalAt` that once
   blocked this are already fixed — `.bvSlt` compares via `toSignedBV`,
   `.bvSDiv` uses `toSignedBV` with T-rounding `Int.div`, and `.bvAShr` uses
   `Int.fdiv` over `toSignedBV` — so the evaluator matches SMT-LIB signed
   semantics and this is no longer a pre-condition for wiring
   `ay_sound_unsat`.

2. **Certificate path (in-repo, ALREADY MODELLED).** The Rust side already owns
   the request/evidence serializer this bridge would feed:
   `trust_ir::request::NativeVerificationRequest::stable_digest()` and
   `NativeVerificationBundle::stable_digest()` produce the deterministic,
   versioned dispatch identity; `ProofEvidence::SmtProof(..)` /
   `ProofCertificateRef` are the certificate slots an ay UNSAT result lands in;
   `ProofObligation::status = Discharged`/`Certified` is the post-check state.
   That path is real today (the `trust-ir-ay` adapter exercises a parallel
   solver-backed version of it). What is missing is the *link*: a checked
   importer that turns an ay proof certificate into a `ProofEvidence` whose
   acceptance discharges the Lean `ay_sound_unsat` premise (replacing the axiom
   with a kernel-checked certificate per "Planned extension 1").

3. **FFI / process invocation (ay-side, OUT OF THIS REPO).** Binding `ay_check`
   via `@[extern]` or a process call requires the ay solver itself, which lives
   in the `ay` repo and is consumed only through the non-default
   `trust-ir-ay` adapter. This repo cannot instantiate it; doing so is the
   cross-repo step gated on (1) and (2).
-/

end TrustIr
