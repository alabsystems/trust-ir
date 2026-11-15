-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Dialect lowering correctness obligation schema.
-- Reference: designs/2026-04-19-dialect-lowering-correctness.md
-- Reference: designs/2026-04-18-ty-supremacy-trust_ir-scope.md section 2.R6, 3.3
-- Reference: crates/trust_ir/src/dialect/mod.rs       (TL4 Rust framework)
-- Reference: crates/trust_ir/src/dialect/inst.rs      (DialectInst)
-- Reference: crates/trust_ir/src/dialect/lowering.rs  (LoweringPass)
--
-- This module formalises the obligation that every producer-side
-- dialect (ty verif.* , a future arith.* , etc.) must discharge:
-- lowering a DialectOpSem to a List Inst must preserve the op's
-- declared semantics. TrustIr ships the schema; concrete dialects ship
-- the witness proofs in their own producer repos.
--
-- Note (TrustIr#54): The non-semantic DialectInst carrier — the payload
-- embedded inside Inst.DialectOp — lives in TrustIr.DialectInst. The
-- DialectOpSem structure below bundles that carrier with a declared
-- denotation (runOp) so concrete dialects can state and prove their
-- lowering-correctness obligations.

import TrustIr.Inst
import TrustIr.Semantics.Step

namespace TrustIr

/-!
# Dialect Lowering Correctness Obligation

A dialect op is a semantic black box from TrustIr's perspective: the op
carries its own declared denotation as a pure function on
MachineState. A lowering rewrites the op into a list of core TrustIr
instructions. The obligation is that running the declared denotation
and running the lowered instruction list are observationally
indistinguishable (the runsAgree relation below).

The Rust dialect framework mirrors the structure here:
  DialectInst          <-> TrustIr.DialectInst (the Inst payload)
                           + DialectOpSem (adds runOp for proofs)
  LoweringPass.rewrite <-> Lowering
  DialectRegistry.lower iterates passes to a fixed point; the per-op
  correctness obligation here is the pointwise condition that makes
  that iteration sound.

## Non-goals

* TrustIr ships no concrete dialect. DummyDialect below is deliberately
  trivial -- it exists only to prove the schema is inhabitable.
* The schema is a forward-simulation obligation for non-terminator
  dialect ops.
* stepInst on Inst.DialectOp is a structured unsupported-subset error by
  design: the core semantics refuses to interpret dialect ops, and
  dialect-aware passes must lower them before evaluation (TrustIr#54).
-/

/-! ## Abstract dialect op -/

/-- A dialect operation carrying its declared semantics.

    The non-semantic fields come from the embedded DialectInst
    carrier, which mirrors Rust DialectInst one-to-one. The semantic
    payload is runOp: a pure function from MachineState to
    Except SemError MachineState. Concrete dialects supply this
    denotation; the TrustIr schema treats it as opaque.

    Design note: the issue phrases the obligation as a Hoare triple
    {pre} op {post}. We carry the denotation instead -- Hoare triples
    are derivable from a denotation but not vice versa. -/
structure DialectOpSem where
  /-- Non-semantic, serializable payload — identical to the carrier
      embedded inside Inst.DialectOp. Producer repos that want their
      lowering proofs to be stated against the actual IR payload can
      package a DialectInst here and supply the declared runOp. -/
  inst  : DialectInst
  /-- Declared semantic function. Running the op on a state s either
      succeeds with a post-state s' or errors in the SemError
      domain shared with Sem. -/
  runOp : MachineState → Except SemError MachineState

namespace DialectOpSem

/-- Dialect namespace of the op. -/
def dialect (d : DialectOpSem) : String := d.inst.dialect

/-- Op name within the dialect. -/
def op (d : DialectOpSem) : String := d.inst.op

end DialectOpSem

/-! ## Running a lowered sequence -/

/-- Execute a list of TrustIr instructions as a straight-line sequence.

    Terminators are disallowed: a dialect op that lowers to a
    terminator falls outside the schema. This matches the Rust
    LoweringPass contract, where a pass produces a Vec of InstrNode
    spliced into the current block (emitting a terminator mid-block
    would break block structure). -/
def runInsts : List Inst → Sem Unit
  | []        => pure ()
  | i :: rest => do
    let r ← stepInst i
    match r with
    | .value _       => runInsts rest
    | .values _      => runInsts rest
    | .terminator _  =>
      Sem.throwTypeError "dialect lowering emitted a terminator"

/-! ## Observational equivalence -/

/-- The dialect op's declared run and the lowered instruction list
    agree observationally on every initial state.

    * If runOp succeeds with post-state s', the lowered run must
      succeed and reach the same post-state s'.
    * If runOp errors with e, the lowered run must error with the
      same e.

    Full MachineState equality is the strongest form of the
    obligation. Concrete dialects whose lowerings introduce fresh
    SSA bindings will typically refine runsAgree to an
    "equal-except-locals" variant (see
    TrustIr.Proofs.TransformCorrectness.state_equiv_except_locals),
    which still refines this form for any observer that does not
    inspect fresh locals. -/
def runsAgree (op : DialectOpSem) (lowered : List Inst) : Prop :=
  ∀ (s : MachineState),
    match op.runOp s with
    | .ok s'   => Sem.run (runInsts lowered) s = .ok ((), s')
    | .error e => Sem.run (runInsts lowered) s = .error e

/-! ## The obligation schema -/

/-- Lowering function type: a dialect-scoped rewriter that may fail
    with a descriptive error string. Mirrors Rust
    LoweringPass.rewrite returning RewriteOutcome. -/
abbrev Lowering := DialectOpSem → Except String (List Inst)

/-- Lowering-correctness obligation for a dialect.

    A producer repo ships a concrete lower : Lowering and a proof
    term of DialectLowerSound d lower. Because runOp is part of
    each DialectOpSem, the obligation is inherently pointwise over
    specific ops: the dialect's canonical op constructors (e.g.
    dummyNoop below, or a future verifBfsStep) pin down runOp
    for each op name, and the lowering is proven correct with
    respect to those constructors. -/
def DialectLowerSound (d : String) (lower : Lowering) : Prop :=
  ∀ (op : DialectOpSem) (lowered : List Inst),
    op.dialect = d →
    lower op = .ok lowered →
    runsAgree op lowered

/-! ## Helper lemma about the empty lowering -/

/-- Reduction lemma: runInsts [] is pure unit at any state. -/
@[simp] theorem runInsts_nil_run (s : MachineState) :
    Sem.run (runInsts []) s = .ok ((), s) := by
  rfl

/-! ## DummyDialect: the inhabitability witness

The schema must not be vacuously true. We ship one concrete op
(dummy.noop) whose declared semantics is the identity on state,
and lower it to the empty instruction list. The resulting
DialectLowerSound proof is a short calculation -- exactly what
producers will copy and specialise to their own ops.

Key modelling move: dummyLower accepts ONLY DialectOpSem values whose
runOp is the identity. This is enforced by a side-condition on
op.runOp rather than by matching on the Rust-mirrored (dialect, op)
name pair alone -- the name pair does not pin down runOp, so a
lowering that ignores runOp cannot in general be correct. Concrete
dialects will use the same pattern: their lower function's ok arm
fires only when the op's runOp matches a known canonical denotation. -/

/-- The canonical dummy.noop operation: identity denotation. -/
def dummyNoop : DialectOpSem :=
  { inst := { dialect   := "dummy"
              op        := "noop"
              operands  := []
              resultTys := []
              attrs     := []
              version   := 1 }
    runOp := fun s => .ok s }

/-- Lowering for DummyDialect.

    Returns ok [] exactly when the op is semantically a dummy.noop:
    dialect name matches, op name matches, AND the declared runOp is
    the identity. Otherwise returns error.

    "runOp is the identity" is expressed via propositional equality
    of the function value. This is the cleanest statement for an MVP
    example; concrete dialects with richer op families will use a
    more structured disambiguator (e.g. an attribute tag, a version
    check, or a case split on op.op with a per-op runOp lemma). -/
noncomputable def dummyLower : Lowering
  | op =>
    open Classical in
    if op.dialect = "dummy" ∧ op.op = "noop"
       ∧ op.runOp = (fun s => .ok s) then
      .ok []
    else
      .error "dummyLower: unknown op or non-canonical runOp"

/-- Headline example. DummyDialect discharges the schema.

    Proof structure:
    1. Unfold dummyLower; the ok [] branch requires
       op.runOp = (fun s => .ok s).
    2. Therefore op.runOp s = .ok s for every s.
    3. runInsts [] = pure (), so Sem.run (runInsts []) s = .ok ((), s).
    4. Both sides of runsAgree reduce to .ok ((), s).

    No proof placeholder. No axiom. -/
theorem dummy_lower_sound : DialectLowerSound "dummy" dummyLower := by
  intro op lowered _hdialect hlow
  -- Split on the if inside dummyLower.
  unfold dummyLower at hlow
  by_cases hcond : op.dialect = "dummy" ∧ op.op = "noop"
                   ∧ op.runOp = (fun s => .ok s)
  · -- Happy path.
    rw [if_pos hcond] at hlow
    -- hlow : Except.ok [] = Except.ok lowered
    injection hlow with hlow'
    subst hlow'
    -- Extract the runOp equality.
    obtain ⟨_, _, hrun⟩ := hcond
    intro s
    -- Rewrite op.runOp to the identity on this specific s.
    rw [hrun]
    -- Both sides reduce to .ok ((), s).
    show Sem.run (runInsts []) s = .ok ((), s)
    exact runInsts_nil_run s
  · -- Sad path: the else branch gives .error, contradicting
    -- hlow : .ok lowered.
    rw [if_neg hcond] at hlow
    exact absurd hlow (by intro h; cases h)

end TrustIr
