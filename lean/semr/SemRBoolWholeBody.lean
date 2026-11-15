/- Copyright 2026 Andrew Yates. Apache-2.0. Original whole-body semantics. -/
import SemRBoolBody
namespace SemR.BoolBody
/-- The whole original function, not an independently authored evaluator.
    All lookups name the actual module and function. The root start constructs
    its own initial memory, empty caller stack and SSA argument bindings. -/
theorem whole_body {m : Module} {function : Func} {fid left right result : Nat} {op : BinOp}
    (found : m.functions.find? (fun f => f.id == fid) = some function)
    (signature : nth? m.funcTys function.ty =
      some { params := [.bool, .bool], returns := [.bool], vararg := false })
    (body : function.blocks = [{ id := function.entry, params := [(left, .bool), (right, .bool)], body := [{ inst := .binop op .bool left right, results := [result] }, { inst := .ret [result], results := [] }] }])
    (opcode : op = .and ∨ op = .bAnd)
    (target : m.executableTarget = true) (distinct : left ≠ right)
    (a b : Bool) (depth : Nat) :
    runFunction m fid [.bool a, .bool b] 2 depth = .ret [.bool (a && b)] := by
  rcases opcode with rfl | rfl <;> simp [runFunction, start, found, signature, body, target, checkSig,
    rejectPoison, expectTy, Val.ty, Ty.beq, bindParams, findBlock,
    run, stepCore, nth?, execNode, binopStep, getV, lookupEnv, evalBinop,
    boolBin, expectBool, isBoolTy, liftOp, bindResults, next, getVs,
    retStep, returnTo, R.bind, Pure.pure, Bind.bind, ofR, Ne.symm distinct]

/-- A derivation over the actual decoded wire subject lifts to the original
    blob execution. Decoding equality is a premise to be independently checked,
    never inferred from a body hash or a sampled execution table. -/
theorem whole_blob {bytes : List Nat} {m : Module} {function : Func}
    {fid left right result : Nat} {op : BinOp}
    (decoded : decode bytes = .ok m)
    (found : m.functions.find? (fun f => f.id == fid) = some function)
    (signature : nth? m.funcTys function.ty =
      some { params := [.bool, .bool], returns := [.bool], vararg := false })
    (body : function.blocks = [{ id := function.entry, params := [(left, .bool), (right, .bool)], body := [{ inst := .binop op .bool left right, results := [result] }, { inst := .ret [result], results := [] }] }])
    (opcode : op = .and ∨ op = .bAnd)
    (target : m.executableTarget = true) (distinct : left ≠ right)
    (a b : Bool) (depth : Nat) :
    runBlob bytes fid [.bool a, .bool b] 2 depth = .ok (.ret [.bool (a && b)]) := by
  unfold runBlob
  rw [decoded]
  exact congrArg Except.ok (whole_body found signature body opcode target distinct a b depth)

/-- The positive and false-goal replay subjects retain the complete original
    lookup, signature, block, target and argument-identity premises. -/
def WholeBodyGoal (combine : Bool → Bool → Bool) : Prop :=
  ∀ {m : Module} {function : Func} {fid left right result : Nat} {op : BinOp},
    m.functions.find? (fun f => f.id == fid) = some function →
    nth? m.funcTys function.ty = some { params := [.bool, .bool], returns := [.bool], vararg := false } →
    function.blocks = [{ id := function.entry, params := [(left, .bool), (right, .bool)], body := [{ inst := .binop op .bool left right, results := [result] }, { inst := .ret [result], results := [] }] }] →
    (op = .and ∨ op = .bAnd) →
    m.executableTarget = true → left ≠ right → ∀ (a b : Bool) (depth : Nat),
    runFunction m fid [.bool a, .bool b] 2 depth = .ret [.bool (combine a b)]

def WholeAndGoal : Prop := WholeBodyGoal (fun a b => a && b)
def WholeOrGoal : Prop := WholeBodyGoal (fun a b => a || b)

/-- A typed canonical-model counterexample; it asserts no Rust/source identity. -/
private def controlFunction : Func :=
  { id := 0, ty := 0, entry := 3, blocks := [{ id := 3, params := [(7, .bool), (11, .bool)], body := [{ inst := .binop .and .bool 7 11, results := [19] }, { inst := .ret [19], results := [] }] }] }

private def controlModule : Module :=
  { funcTys := [{ params := [.bool, .bool], returns := [.bool], vararg := false }], enums := [], functions := [controlFunction] }

theorem whole_or_counterexample : ¬ WholeOrGoal := by
  intro wrong
  have impossible := wrong (m := controlModule) (function := controlFunction)
    (fid := 0) (left := 7) (right := 11) (result := 19) (op := .and)
    rfl rfl rfl (Or.inl rfl) rfl (by decide) true false 0
  cases impossible

end SemR.BoolBody
