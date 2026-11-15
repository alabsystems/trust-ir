-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.Monad
import TrustIr.Semantics.IntRepresentation

namespace TrustIr

/-- Read the declared integer bit pattern. Signed interpretation is separate
    from consumer-specific validity policies and nonnegative-index guards. -/
def typedIntegerValue (model : ByteModel) (ty : Ty) (value : Value) :
    Except SemError Int := do
  if value.isPoison || value.isUninit then
    throw (.ub "typed integer: use of an uninitialized operand")
  if !ty.isInteger then throw (.typeError "typed integer: declaration is not an integer")
  let expected ← match ty.bitWidthFor model with
    | some width => pure width
    | none => throw (.typeError "typed integer: declaration has no width")
  match value with
  | .int width raw =>
    if width != expected then throw (.typeError "typed integer: carrier width mismatch")
    let residue := truncateUnsigned raw expected
    pure (if ty.isSigned then toSigned residue expected else residue)
  | _ => throw (.typeError "typed integer: operand is not an integer")

/-- Index consumers reject negative integers after their declared signedness
    has been interpreted. This guard is deliberately absent from the reader. -/
def nonnegativeElementIndex (value : Int) : Except SemError Nat :=
  if value < 0 then .error (.ub "negative element index") else .ok value.toNat


/-- The runtime integer carrier also includes Char. Unicode validity belongs
    to SSA binding, not to integer use; Char has the unsigned 32-bit carrier. -/
def typedIntegerCarrierValue (model : ByteModel) (ty : Ty) (value : Value) :
    Except SemError Int :=
  typedIntegerValue model (match ty with | .Char => .U32 | other => other) value

abbrev IntegerOperandReader := ValueId → Value → Except SemError Int

def unknownIntegerOperand (_ : ValueId) (value : Value) : Except SemError Int :=
  if value.isPoison || value.isUninit then
    .error (.ub "integer operand: use of an uninitialized value")
  else .error (.unsupported .ssaTypeTable "integer operand requires its original declaration")

/-- Keep the u64 bound as a compiled computation. A folded 2^64 stores an
    mpz whose uninitialized padding makes Lean4.8 OLeans nondeterministic;
    the existing Sem.addrBits boundary in Cast uses the same remedy. -/
@[noinline] def word64Bits : Nat := 64

def word64Limit : Nat := 2 ^ word64Bits

/-- The compilation boundary does not change the mathematical word limit. -/
theorem word64Limit_eq_pow : word64Limit = 2 ^ 64 := rfl

def word64Max : Nat := word64Limit - 1

/-- Word conversion occurs before multiplication, including zero-sized types. -/
def checkedWord64Operand (op : String) (positive : Bool) (value : Int) :
    Except SemError Nat :=
  if value < 0 || (positive && value == 0) then
    .error (.ub (trustIrStringBuild s!"{op}: integer operand is outside its nonnegative/positive domain"))
  else if value > (word64Max : Int) then
    .error (.ub (trustIrStringBuild s!"{op}: integer operand exceeds u64"))
  else .ok value.toNat

def checkedWord64Mul (op : String) (left right : Nat) : Except SemError Nat :=
  if left * right ≤ word64Max then .ok (left * right)
  else .error (.ub (trustIrStringBuild s!"{op}: byte size multiplication overflows u64"))

def checkedWord64Add (op : String) (left right : Nat) : Except SemError Nat :=
  if left + right ≤ word64Max then .ok (left + right)
  else .error (.ub (trustIrStringBuild s!"{op}: byte offset addition overflows u64"))

end TrustIr

#trustIrAxiomsExact TrustIr.checkedWord64Operand == []
#trustIrAxiomsExact TrustIr.checkedWord64Mul == []
#trustIrAxiomsExact TrustIr.checkedWord64Add == []
