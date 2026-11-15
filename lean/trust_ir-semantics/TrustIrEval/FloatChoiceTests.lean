-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIrRuntime
import TrustIrEval.Run

open TrustIr TrustIrEval

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def signWord : Int := 9223372036854775808

private def intsAre (values : List Value) (wanted : List Int) : Bool :=
  values.length == wanted.length && (values.zip wanted).all (fun (value, raw) =>
    match value with | .int 64 actual => actual == raw | _ => false)

private def block (params : List Ty) (body : List Inst) (returns : List ValueId) : BasicBlock :=
  { params := (trustIrEntryEnumFrom 0 params).map (fun (index, ty) => (⟨index⟩, ty))
    body := body
    bodyResultDests := (trustIrEntryEnumFrom 0 body).map (fun (index, _) => [⟨params.length + index⟩])
    terminator := .Return returns }

private def cfg (body : BasicBlock) : CFG := fun id =>
  if id.index == 0 then some body else none

/-- Two dynamic occurrences separated by a real call. Returned integer bits
    observe both signs, so numerical zero equality cannot hide a lost choice. -/
private def callContext (model : ByteModel) : EvalContext :=
  let root : EvalFunction :=
    { body := { paramTys := [], returnTys := [.U64, .U64] }
      entryBlock := ⟨0⟩
      cfg := cfg (block []
        [.Const .F64 (.float 0.0), .Const .F64 (.float (-0.0)),
         .BinOp .FMin .F64 ⟨0⟩ ⟨1⟩, .Cast .Bitcast .F64 .U64 ⟨2⟩,
         .Call ⟨1⟩ [⟨0⟩, ⟨1⟩]] [⟨3⟩, ⟨4⟩]) }
  let callee : EvalFunction :=
    { body := { paramTys := [.F64, .F64], returnTys := [.U64] }
      entryBlock := ⟨0⟩
      cfg := cfg (block [.F64, .F64]
        [.BinOp .FMax .F64 ⟨0⟩ ⟨1⟩, .Cast .Bitcast .F64 .U64 ⟨2⟩] [⟨3⟩]) }
  { EvalContext.empty with
    byteModel := model
    maxCallDepth := 1
    functions := fun id =>
      if id.index == 0 then some root else if id.index == 1 then some callee else none }

private def vectorBits : Sem (List Value) := do
  let result ← semBinOp .FMin (.Vector 2 .F64) ⟨0⟩ ⟨1⟩
  let value ← Sem.lookupValue result
  let values ← match value with
    | .vector values => pure values
    | _ => Sem.throwTypeError "min/max did not return a vector"
  values.mapM (fun value => do
    let id ← Sem.bindFresh value
    let bits ← semCast .Bitcast .F64 .U64 id
    Sem.lookupValue bits)

/-- A callee consumes a choice and then raises. The handler must continue
    with the next choice while observing the caller's original result. -/
private def unwindContext (model : ByteModel) : EvalContext :=
  let caller : EvalFunction :=
    { body := { paramTys := [], returnTys := [.U64, .U64] }
      entryBlock := ⟨0⟩
      cfg := fun id =>
        if id.index == 0 then
          some { params := [],
                 body := [.Const .F64 (.float 0.0), .Const .F64 (.float (-0.0)),
                   .BinOp .FMin .F64 ⟨0⟩ ⟨1⟩, .Cast .Bitcast .F64 .U64 ⟨2⟩],
                 bodyResultDests := [[⟨0⟩], [⟨1⟩], [⟨2⟩], [⟨3⟩]],
                 terminator := .Invoke ⟨1⟩ [⟨0⟩, ⟨1⟩] ⟨1⟩ [] ⟨2⟩ }
        else if id.index == 1 then
          some { params := [], body := [], terminator := .Unreachable }
        else if id.index == 2 then
          some { params := [],
                 body := [.LandingPad false [0], .Const .F64 (.float 0.0),
                   .Const .F64 (.float (-0.0)), .BinOp .FMax .F64 ⟨102⟩ ⟨103⟩,
                   .Cast .Bitcast .F64 .U64 ⟨104⟩],
                 bodyResultDests := [[⟨100⟩, ⟨101⟩], [⟨102⟩], [⟨103⟩], [⟨104⟩], [⟨105⟩]],
                 terminator := .Return [⟨3⟩, ⟨105⟩] }
        else none }
  let callee : EvalFunction :=
    { body := { paramTys := [.F64, .F64], returnTys := [] }
      entryBlock := ⟨0⟩
      cfg := fun id => if id.index == 0 then
        some { params := [(⟨0⟩, .F64), (⟨1⟩, .F64)],
               body := [.BinOp .FMax .F64 ⟨0⟩ ⟨1⟩, .Const .Bool (.bool false),
                 .Assert ⟨3⟩ .DivByZero none],
               bodyResultDests := [[⟨2⟩], [⟨3⟩], []],
               terminator := .Return [] }
        else none }
  { EvalContext.empty with
    byteModel := model
    maxCallDepth := 1
    functions := fun id =>
      if id.index == 0 then some caller else if id.index == 1 then some callee else none }

def main : IO Unit := do
  let mut controls := 0
  for model in [ByteModel.le32, .le64] do
    for first in [false, true] do
      for raised in [false, true] do
        for last in [false, true] do
          let initial := MachineState.empty.withFloatZeroChoices (.ofList [first, raised, last])
          let wanted := [if first then 0 else signWord, if last then 0 else signWord]
          require "choice consumption survives invoke, callee raise and caller handler"
            (match Sem.run (evalFunctionInContext (unwindContext model) ⟨0⟩ [] 8 .unwind) initial with
             | .ok (values, final) => intsAre values wanted && final.floatZeroChoiceCursor == 3
             | _ => false)
          controls := controls + 1
    require "zero call-depth budget still refuses the same call"
      (match Sem.run (evalFunctionInContext { callContext model with maxCallDepth := 0 }
          ⟨0⟩ [] 4) MachineState.empty with
       | .error .outOfFuel => true
       | _ => false)
    controls := controls + 1
    for first in [false, true] do
      for second in [false, true] do
        let state := MachineState.empty.withFloatZeroChoices
          (.ofList [first, second])
        let wanted := [if first then 0 else signWord, if second then 0 else signWord]
        let callResult := Sem.run (evalFunctionInContext (callContext model) ⟨0⟩ [] 4) state
        match callResult with
        | .ok (values, final) =>
          unless intsAre values wanted && final.floatZeroChoiceCursor == 2 do
            IO.println s!"model={repr model} choices={first}/{second} actual={repr values} wanted={repr wanted} cursor={final.floatZeroChoiceCursor}"
        | .error error => IO.println s!"call error: {repr error}"
        require "independent zero choices survive a real call and bit observation"
          (match callResult with
           | .ok (values, final) => intsAre values wanted && final.floatZeroChoiceCursor == 2
           | _ => false)
        let vectorState := { state with
          locals := ValueMap.empty.set ⟨0⟩ (.vector [.float 0.0, .float 0.0])
            |>.set ⟨1⟩ (.vector [.float (-0.0), .float (-0.0)])
          nextValueId := 2 }
        require "identical vector lanes have independent observable choices"
          (match Sem.run vectorBits vectorState with
           | .ok (values, final) => intsAre values wanted && final.floatZeroChoiceCursor == 2
           | _ => false)
        controls := controls + 2
    for op in [BinOp.FMin, .FMax] do
      for (left, right) in [(0.0, 0.0), (-0.0, -0.0), (1.0, -0.0), (0.0 / 0.0, -0.0)] do
        require "non-ambiguous min/max does not consume a choice"
          (match Sem.run (semFloatMinMaxAt op .F64 left right)
              (MachineState.empty.withFloatZeroChoices (.ofList [true])) with
           | .ok (_, final) => final.floatZeroChoiceCursor == 0
           | _ => false)
        controls := controls + 1
  IO.println s!"Min/max choice runtime: {controls} call/lane/sign and consumption controls passed"
