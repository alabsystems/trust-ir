/- Copyright 2026 Andrew Yates. Apache-2.0.
   Checked root invocations of original decoded Boolean bodies. No source,
   arbitrary-caller, shared-heap or machine-code correspondence is asserted. -/
import SemRBoolWholeBody

namespace SemR.BoolBody

structure ConjunctionWitness (m : Module) (fid : Nat) where
  function : Func
  left : Nat
  right : Nat
  result : Nat
  op : BinOp
  found : m.functions.find? (fun f => f.id == fid) = some function
  signature : nth? m.funcTys function.ty = some { params := [.bool, .bool], returns := [.bool], vararg := false }
  body : function.blocks = [{ id := function.entry, params := [(left, .bool), (right, .bool)], body := [{ inst := .binop op .bool left right, results := [result] }, { inst := .ret [result], results := [] }] }]
  opcode : op = .and ∨ op = .bAnd
  target : m.executableTarget = true
  distinct : left ≠ right

def conjunctionOp : BinOp → Bool
  | .and | .bAnd => true
  | _ => false

theorem conjunctionOp_sound {op : BinOp} (h : conjunctionOp op = true) :
    op = .and ∨ op = .bAnd := by
  cases op <;> simp_all [conjunctionOp]

/-- The original decoded function is read independently of every native
    reader result. Success carries proofs of all original execution premises. -/
def checkConjunction (m : Module) (fid : Nat) : Option (ConjunctionWitness m fid) :=
  if ht : m.executableTarget = true then
    match hf : m.functions.find? (fun f => f.id == fid) with
    | some f =>
      match hs : nth? m.funcTys f.ty with
      | some ⟨[.bool, .bool], [.bool], false⟩ =>
        match hb : f.blocks with
        | [⟨entry, [(left, .bool), (right, .bool)],
            [⟨.binop op .bool lhs rhs, [result]⟩, ⟨.ret [returned], []⟩]⟩] =>
          if he : entry = f.entry then
            if hl : lhs = left then
              if hr : rhs = right then
                if hv : returned = result then
                  if hd : left ≠ right then
                    if ho : conjunctionOp op = true then
                      some {
                        function := f
                        left := left
                        right := right
                        result := result
                        op := op
                        found := hf
                        signature := hs
                        body := by simpa [he, hl, hr, hv] using hb
                        opcode := conjunctionOp_sound ho
                        target := ht
                        distinct := hd
                      }
                    else none
                  else none
                else none
              else none
            else none
          else none
        | _ => none
      | _ => none
    | none => none
  else none

/-- Acceptance proves the complete original root invocation, through original
    start, SSA parameter binding, two operational steps and original return. -/
theorem checked_body {m : Module} {fid : Nat}
    (accepted : (checkConjunction m fid).isSome = true)
    (a b : Bool) (depth : Nat) :
    runFunction m fid [.bool a, .bool b] 2 depth = .ret [.bool (a && b)] := by
  let witness := (checkConjunction m fid).get accepted
  exact whole_body witness.found witness.signature witness.body witness.opcode
    witness.target witness.distinct a b depth

theorem except_success {ε α : Type} (value : Except ε α)
    (success : value.toOption.isSome = true) :
    value = .ok (value.toOption.get success) := by
  cases value with
  | error e => cases success
  | ok a => rfl

/-- Two closed Boolean facts suffice to check an actual byte subject. The
    decoder-success fact and body-acceptance fact must themselves kernel-check;
    neither a native parser nor a proposed model value supplies an assumption. -/
theorem checked_blob {bytes : List Nat} {fid : Nat}
    (decoded : (decode bytes).toOption.isSome = true)
    (accepted : (checkConjunction ((decode bytes).toOption.get decoded) fid).isSome = true)
    (a b : Bool) (depth : Nat) :
    runBlob bytes fid [.bool a, .bool b] 2 depth = .ok (.ret [.bool (a && b)]) := by
  unfold runBlob
  rw [except_success (decode bytes) decoded]
  exact congrArg Except.ok (checked_body accepted a b depth)

end SemR.BoolBody
