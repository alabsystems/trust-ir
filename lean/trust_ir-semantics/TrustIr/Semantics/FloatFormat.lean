-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Float-format fidelity for the executable semantics: which float values
-- inhabit which float TYPE, how a result is rounded to its type, and the byte
-- image a float has in memory. Every width-sensitive float rule in
-- `Semantics/` routes through the helpers here, so the model cannot compute a
-- narrower type at binary64 or fabricate a byte image by accident.
--
-- Roadmap WS2.23 (docs/ub-numerics-policy.md §2, §7 item 6).

import TrustIr.Semantics.Monad

namespace TrustIr

/-!
# Float formats

`Value.float` carries one Lean `Float` (IEEE binary64) whatever the static
type. A value of type `F32` is therefore well formed only when that binary64
number is exactly a binary32 number, and every operation whose RESULT type is
`F32` rounds to binary32 exactly once.

## The rounder

`roundDyadic` rounds an EXACT dyadic rational `m·2^e` to an IEEE binary
format, round-to-nearest-even, in `Nat` arithmetic: it keeps `p` significand
bits, flushes gradually below the minimum normal exponent (the quantum never
drops under `2^qmin`, `qmin = emin - (p-1)`, so subnormals come out exactly),
and `overflows` sends a result at or above `2^(emax+1)` to infinity — for
binary32 that is exactly the RNE threshold `(2 - 2^-24)·2^127`. Its input is
exact: a finite `Float` decomposes exactly as `m·2^(e-53)` through `frExp`
(`floatDyadic`, the idiom `floatFRem` and `floatTruncNat` already rely on),
and an integer is `|i|·2^0`. So `roundToFormat` rounds a binary64 value ONCE,
and `roundIntToFormat` rounds an integer ONCE — never through a wider float
intermediate, which could double-round.

Why one rounding of the binary64 result is the binary32 result: for binary32
operands, the binary64 `+ - * /` result is rounded from the exact result at
precision 53 ≥ 2·24 + 2, which makes rounding it again to 24 bits equal to
rounding the exact result once (Figueroa). `FRem` is exact before rounding,
and `FNeg` is exact.

## Byte images

`encodeBits` / `decodeBits` are the IEEE interchange encodings: sign,
biased exponent, fraction; subnormals, `±0`, `±inf`. Lean 4.8.0 has no
`Float.toBits` / `Float.ofBits`, so a NaN's payload and sign are not
observable in the model. `encodeBits` renders every NaN as the canonical quiet
NaN (`0x7fc00000` / `0x7ff8000000000000`) for fixture rendering only; every
path that would EXPOSE a NaN's bits to the program refuses with
`unsupported.float` instead: a bitcast float → int (`floatToBitsAt`), and a
STORE of a NaN (`encodeFloatAt`) — the stored bytes can be reloaded at an
integer type, and the real program's bytes are the NaN's actual payload and
sign (a bitcast-made signalling NaN, `fneg` of a NaN, the host's default NaN),
which a canonical image would contradict. A NaN image written by the program
itself (integer store, float load) decodes to a NaN. That residue is recorded
on the B3 depth ledger.

## What still refuses

Binary16 arithmetic, byte images and bitcasts use the same parametric
format machinery as binary32 and binary64. Observable NaN payloads still
refuse at every width. Subset admission and native lowering are separate
contracts; executable semantics alone does not change their versions.
-/

/-- The parameters of an IEEE 754 binary interchange format. -/
structure BinaryFormat where
  /-- Significand precision `p`, hidden bit included. -/
  precision : Nat
  /-- Width of the biased-exponent field. -/
  expBits : Nat
  deriving Repr

namespace BinaryFormat

def binary16 : BinaryFormat := ⟨11, 5⟩
def binary32 : BinaryFormat := ⟨24, 8⟩
def binary64 : BinaryFormat := ⟨53, 11⟩

/-- Stored fraction bits, `p - 1`. -/
def fracBits (f : BinaryFormat) : Nat := f.precision - 1
/-- Exponent bias, which is also `emax`. -/
def bias (f : BinaryFormat) : Nat := 2 ^ (f.expBits - 1) - 1
/-- The all-ones exponent field (infinities and NaNs). -/
def expAllOnes (f : BinaryFormat) : Nat := 2 ^ f.expBits - 1
/-- Exponent of the least significant bit of the smallest subnormal:
    `emin - (p - 1)` with `emin = 1 - emax` (`-149` for binary32, `-1074` for
    binary64). No finite value of the format has a finer quantum. -/
def qmin (f : BinaryFormat) : Int := 1 - (f.bias : Int) - (f.fracBits : Int)

end BinaryFormat

/-- Positive infinity. -/
def floatPosInf : Float := 1.0 / 0.0
/-- A quiet NaN (the model cannot observe which one). -/
def floatNaN : Float := 0.0 / 0.0

/-- Exact decomposition of a finite nonzero `Float`: `|f| = m·2^e` with
    `m ∈ [2^52, 2^53)` from the `frExp` normalization (subnormals included). -/
def floatDyadic (f : Float) : Nat × Int :=
  let (frac, ex) := f.abs.frExp
  ((frac.scaleB 53).toUInt64.toNat, ex - 53)

/-- The binary64 value `r·2^q`, exact whenever it is binary64-representable
    (`r ≤ 2^53`, so `Float.ofNat` is exact and `scaleB` is C `scalbn`). -/
def dyadicToFloat (r : Nat) (q : Int) : Float := (Float.ofNat r).scaleB q

/-- Round the exact positive dyadic `m·2^e` (`m > 0`) to `fmt`,
    round-to-nearest-even. Returns `(r, q, exact)`: the rounded magnitude is
    `r·2^q`, and `exact` says no bit was discarded. The quantum `q` is the
    format's ulp at the value's binade, floored at `qmin`, so subnormal
    results are produced by the same rounding step (gradual underflow).
    Overflow is NOT decided here (`overflows`). -/
def roundDyadic (fmt : BinaryFormat) (m : Nat) (e : Int) : Nat × Int × Bool :=
  let top : Int := e + (Nat.log2 m : Int)
  let q : Int := max (top - (fmt.fracBits : Int)) fmt.qmin
  if q ≤ e then
    (m <<< (e - q).toNat, q, true)
  else
    let sh := (q - e).toNat
    let r := m >>> sh
    let rem := m % 2 ^ sh
    let half := 2 ^ (sh - 1)
    let up := rem > half || (rem == half && r % 2 == 1)
    (if up then r + 1 else r, q, rem == 0)

/-- Does the rounded magnitude `r·2^q` reach `2^(emax+1)`, i.e. overflow the
    format to infinity? -/
def overflows (fmt : BinaryFormat) (r : Nat) (q : Int) : Bool :=
  r != 0 && (Nat.log2 r : Int) + q > (fmt.bias : Int)

/-- Round a binary64 value to `fmt` exactly once (RNE). NaN, `±inf` and `±0`
    are preserved; the sign of a result that underflows to zero is kept. -/
def roundToFormat (fmt : BinaryFormat) (f : Float) : Float :=
  if f.isNaN || f.isInf || f == 0.0 then f
  else
    let (m, e) := floatDyadic f
    let (r, q, _) := roundDyadic fmt m e
    let mag := if overflows fmt r q then floatPosInf else dyadicToFloat r q
    if f < 0.0 then -mag else mag

/-- Round an exact integer to `fmt` exactly once (RNE) — the `as`-cast
    semantics, with no wider float intermediate. -/
def roundIntToFormat (fmt : BinaryFormat) (i : Int) : Float :=
  if i == 0 then 0.0
  else
    let (r, q, _) := roundDyadic fmt i.natAbs 0
    let mag := if overflows fmt r q then floatPosInf else dyadicToFloat r q
    if i < 0 then -mag else mag

/-- Is the binary64 value `f` exactly a value of `fmt`? NaN and `±inf` are;
    a finite value is when rounding it to `fmt` discards nothing and does not
    overflow. -/
def isExactIn (fmt : BinaryFormat) (f : Float) : Bool :=
  if f.isNaN || f.isInf || f == 0.0 then true
  else
    let (m, e) := floatDyadic f
    let (r, q, exact) := roundDyadic fmt m e
    exact && !overflows fmt r q

/-- Is `f` negative, `-0.0` included? -/
def floatSignBit (f : Float) : Bool :=
  f < 0.0 || (f == 0.0 && 1.0 / f < 0.0)

/-- The IEEE interchange bit pattern of `f` in `fmt`, or `none` when `f` is
    not exactly a value of `fmt`. Every NaN encodes as the canonical quiet NaN
    (payload unobservable in Lean 4.8.0; see the module docstring). -/
def encodeBits (fmt : BinaryFormat) (f : Float) : Option Nat :=
  let fb := fmt.fracBits
  let signBit : Nat := if floatSignBit f then 2 ^ (fmt.expBits + fb) else 0
  if f.isNaN then some ((fmt.expAllOnes <<< fb) + 2 ^ (fb - 1))
  else if f.isInf then some (signBit + (fmt.expAllOnes <<< fb))
  else if f == 0.0 then some signBit
  else
    let (m, e) := floatDyadic f
    let (r, q, exact) := roundDyadic fmt m e
    if !exact || overflows fmt r q then none
    else if r ≥ 2 ^ fb then
      -- Normal: `r ∈ [2^fb, 2^(fb+1))`, leading-bit exponent `q + fb`.
      some (signBit + ((q + (fb : Int) + (fmt.bias : Int)).toNat <<< fb) + (r - 2 ^ fb))
    else
      -- Subnormal: `q = qmin`, biased exponent 0, the fraction is `r`.
      some (signBit + r)

/-- The value of an IEEE interchange bit pattern of `fmt` (only the low
    `1 + expBits + fracBits` bits are read). Any NaN pattern decodes to a NaN. -/
def decodeBits (fmt : BinaryFormat) (bits : Nat) : Float :=
  let fb := fmt.fracBits
  let frac := bits % 2 ^ fb
  let biased := (bits >>> fb) % 2 ^ fmt.expBits
  let neg := (bits >>> (fb + fmt.expBits)) % 2 == 1
  let mag : Float :=
    if biased == fmt.expAllOnes then (if frac == 0 then floatPosInf else floatNaN)
    else if biased == 0 then dyadicToFloat frac fmt.qmin
    else dyadicToFloat (frac + 2 ^ fb) ((biased : Int) - (fmt.bias : Int) - (fb : Int))
  if neg then -mag else mag

/-- `n` little-endian bytes of the natural number `v` (low bytes kept). -/
def natToBytesLE : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, v => UInt8.ofNat (v % 256) :: natToBytesLE n (v / 256)

/-- The natural number a little-endian byte list denotes. -/
def natOfBytesLE : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * natOfBytesLE rest

/-- The float type's value check: does the runtime `Float` inhabit `ty`?
    `F64` admits every binary64 value; `F32` admits exactly the binary32
    values (anything else is an ill-typed value, a type error). `F16` likewise
    admits exactly binary16 values. A non-float type is a type
    error. -/
def checkFloatAt (ty : Ty) (v : Float) : Except SemError Unit :=
  match ty with
  | .F64 => .ok ()
  | .F32 =>
    if isExactIn .binary32 v then .ok ()
    else .error (.typeError "F32 value is not a binary32 value")
  | .F16 =>
    if isExactIn .binary16 v then .ok ()
    else .error (.typeError "F16 value is not a binary16 value")
  | _ => .error (.typeError s!"float value at non-float type {repr ty}")

/-- Round an exact-or-binary64 result to the float type `ty`, exactly once:
    the identity at `F64`, rounding to binary32 at `F32` and binary16 at `F16`. -/
def roundFloatAt (ty : Ty) (v : Float) : Except SemError Float :=
  match ty with
  | .F64 => .ok v
  | .F32 => .ok (roundToFormat .binary32 v)
  | .F16 => .ok (roundToFormat .binary16 v)
  | _ => .error (.typeError s!"float result at non-float type {repr ty}")

/-- Convert an exact integer to the float type `ty` (`UIToFP`/`SIToFP`),
    rounding the integer itself once (RNE) — at `F64` too, where the former
    `Float.ofInt` truncated magnitudes past 2^64 before rounding. Binary16 uses the same exact integer rounder. -/
def roundIntToFloatAt (ty : Ty) (i : Int) : Except SemError Float :=
  match ty with
  | .F64 => .ok (roundIntToFormat .binary64 i)
  | .F32 => .ok (roundIntToFormat .binary32 i)
  | .F16 => .ok (roundIntToFormat .binary16 i)
  | _ => .error (.typeError s!"int-to-float cast to non-float type {repr ty}")

/-- The runtime value of a float `Const` of type `ty`: the binary64 literal
    rounded to `ty` once (Rust `value as f32`; the interpreter's
    `float_bits_from_f64`). Total, so a `Const` always evaluates. -/
def constFloatAt (ty : Ty) (v : Float) : Float :=
  match ty with
  | .F32 => roundToFormat .binary32 v
  | .F16 => roundToFormat .binary16 v
  | _ => v

/-- The little-endian IEEE byte image of a float stored at `ty`: 8 bytes of
    binary64 at `F64`, 4 bytes of binary32 at `F32` (a value that is not a
    binary32 value is ill-typed and refused, never silently rounded), and
    2 bytes of binary16 at `F16`. A NaN refuses too: its payload and sign are not observable in
    Lean 4.8.0, and the image is observable (reload the cell at an integer
    type), so a canonical image would be a fabricated one. -/
def encodeFloatAt (ty : Ty) (v : Float) : Except SemError (List UInt8) :=
  if v.isNaN then
    .error (.unsupported .float "NaN byte image unobservable (no Float.toBits in Lean 4.8.0)")
  else
  match ty with
  | .F64 =>
    match encodeBits .binary64 v with
    | some bits => .ok (natToBytesLE 8 bits)
    | none => .error (.typeError "F64 value is not a binary64 value")
  | .F32 =>
    match encodeBits .binary32 v with
    | some bits => .ok (natToBytesLE 4 bits)
    | none => .error (.typeError "F32 value is not a binary32 value")
  | .F16 =>
    match encodeBits .binary16 v with
    | some bits => .ok (natToBytesLE 2 bits)
    | none => .error (.typeError "F16 value is not a binary16 value")
  | _ => .error (.typeError s!"float value stored at non-float type {repr ty}")

/-- Decode a little-endian IEEE byte image read at `ty` (the inverse of
    `encodeFloatAt`; a NaN image decodes to a NaN). -/
def decodeFloatAt (ty : Ty) (bytes : List UInt8) : Except SemError Float :=
  match ty with
  | .F64 =>
    if bytes.length == 8 then .ok (decodeBits .binary64 (natOfBytesLE bytes))
    else .error (.typeError "F64 image is not 8 bytes")
  | .F32 =>
    if bytes.length == 4 then .ok (decodeBits .binary32 (natOfBytesLE bytes))
    else .error (.typeError "F32 image is not 4 bytes")
  | .F16 =>
    if bytes.length == 2 then .ok (decodeBits .binary16 (natOfBytesLE bytes))
    else .error (.typeError "F16 image is not 2 bytes")
  | _ => .error (.typeError s!"float decode at non-float type {repr ty}")

/-- `Bitcast` of an integer's bits to the float type `ty` (the low bits of
    the two's-complement residue are the IEEE pattern). -/
def floatFromBitsAt (ty : Ty) (bits : Int) : Except SemError Float :=
  match ty with
  | .F64 => .ok (decodeBits .binary64 (bits % 2 ^ 64).toNat)
  | .F32 => .ok (decodeBits .binary32 (bits % 2 ^ 32).toNat)
  | .F16 => .ok (decodeBits .binary16 (bits % 2 ^ 16).toNat)
  | _ => .error (.typeError s!"float bitcast to non-float type {repr ty}")

/-- `Bitcast` of a float of type `ty` to its IEEE bit pattern. A NaN refuses:
    its payload and sign are not observable in Lean 4.8.0, so answering the
    canonical pattern could disagree with the real bits. -/
def floatToBitsAt (ty : Ty) (v : Float) : Except SemError Nat :=
  if v.isNaN then
    .error (.unsupported .float "NaN payload unobservable (no Float.toBits in Lean 4.8.0)")
  else
    match ty with
    | .F64 =>
      match encodeBits .binary64 v with
      | some bits => .ok bits
      | none => .error (.typeError "F64 value is not a binary64 value")
    | .F32 =>
      match encodeBits .binary32 v with
      | some bits => .ok bits
      | none => .error (.typeError "F32 value is not a binary32 value")
    | .F16 =>
      match encodeBits .binary16 v with
      | some bits => .ok bits
      | none => .error (.typeError "F16 value is not a binary16 value")
    | _ => .error (.typeError s!"float bitcast from non-float type {repr ty}")

end TrustIr
