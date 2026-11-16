-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYTypedRequest

namespace TrustIr.TrustIrExpr

def SMTSort.irValue : (sort : SMTSort) → sort.CoreValue → Value
  | .bool, value => .bool value
  | .bv bits, value => .int bits (Int.ofNat value.toNat)

/-- A checked constant retains the exact original carrier, rather than silently
normalizing a noncanonical source value. -/
structure SMTSourceInput (sort : SMTSort) (value : Value) where
  arg : SMTCheckedTerm sort
  same : sort.irValue (arg.term.eval SMTEnv.default) = value

def SMTSourceInput.build (sort : SMTSort) (value : Value) : Except String (SMTSourceInput sort value) :=
  match sort,value with
  | .bool,.bool value => .ok ⟨SMTCheckedTerm.boolConst value,rfl⟩
  | .bv bits,.int width value =>
    if sameWidth : width = bits then
      if positive : 0 < bits then
        if canonical : Int.ofNat (BitVec.ofInt bits value).toNat = value then
          .ok ⟨⟨.bvConst bits value,[],positive,rfl,[],rfl⟩,by
            simp only [SMTTerm.eval,SMTSort.irValue]
            rw [canonical,sameWidth]⟩
        else .error "SMT source requires a canonical integer carrier"
      else .error "SMT source width must be positive"
    else .error "SMT source carrier width differs from the declared source"
  | _,_ => .error "SMT source carrier differs from the declared source"

end TrustIr.TrustIrExpr
