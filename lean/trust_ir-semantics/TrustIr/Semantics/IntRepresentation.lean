-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.State.ValueMap

/-! Shared integer representation used by memory and arithmetic semantics.

Memory needs the signed interpretation of an index/count, not the integer
operation evaluator. Keep that dependency separate so the canonical byte
memory can also be imported by SemR's pinned reference-kernel toolchain.
The definitions and their fully qualified names are unchanged. Coroutine's
constant construction also retains Value.intAt through the memory import.
-/

namespace TrustIr

/-- Truncate an integer to `width` bits using modular arithmetic.
    For width w, the result is in [0, 2^w). -/
def truncateUnsigned (val : Int) (width : Nat) : Int :=
  val % (2 ^ width)

/-- Interpret an unsigned integer as signed (two's complement).
    For width w: values >= 2^(w-1) are negative. -/
def toSigned (val : Int) (width : Nat) : Int :=
  let half := (2 : Int) ^ (width - 1)
  let modulus := (2 : Int) ^ width
  let uval := val % modulus
  if uval >= half then uval - modulus else uval

/-- THE integer representation of the model: the `w`-bit value of the integer
    literal `i` is its RESIDUE `i mod 2^w`, in `[0, 2^w)`. Parameters
    (`TrustIrEval/Run.lean` `argValue`) and every operation result (`wrap`,
    `truncateUnsigned`) already are residues; every place where a
    `Constant.int` becomes a model value goes through this function, so the
    model has one spelling of each integer (before, a `Const` bound the raw
    literal: `Value.int 32 (-1)` beside `Value.int 32 4294967295`, and every
    consumer that reads the raw `Int` — the unsigned compares and divisions,
    the shift-amount guard, `ZExt`, `UIToFP`, `IntToPtr`, `CmpXchg` — disagreed
    with the reference interpreter on a negative literal). A consumer that
    needs a SIGNED reading takes it explicitly with `toSigned`: the signed
    operations by their opcode (`semICmp`'s signed predicates, `SDiv`, `SRem`,
    `AShr`, the signed overflow checks, `SExt`, `SIToFP`, and `AtomicRMW`'s
    `Max` / `Min`, which until 2026-09-30 ordered the raw `Int`s and so, on
    residues, were `UMax` / `UMin`), and the consumers whose signedness no
    opcode names (`semGEP`'s index, the allocation count, `semCoroSuspend`'s
    immediates). That list is a census by reading (order comparisons and sign
    tests on a model integer in `Semantics/`, 2026-09-30), not a mechanical
    check. The residue bound is `intAt_residue`
    (`TrustIr/Proofs/IntResidue.lean`). -/
def Value.intAt (w : Nat) (i : Int) : Value :=
  .int w (truncateUnsigned i w)

end TrustIr
