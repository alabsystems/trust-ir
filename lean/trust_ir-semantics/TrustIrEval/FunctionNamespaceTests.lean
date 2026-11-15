-- Copyright 2026 Andrew Yates | Author: Andrew Yates | Apache-2.0
-- Executable runner regressions, not proof certificates.
-- Run: lake env lean --run TrustIrEval/FunctionNamespaceTests.lean
import TrustIrRuntime
import TrustIrEval.Run

open TrustIr TrustIrEval Lean

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def entryId : FuncId := ⟨40000⟩

private def fixtureBlock (globalFirst : Bool) : BasicBlock :=
  if globalFirst then
    { params := []
      body := [.GlobalAddr ⟨0⟩, .Cast .PtrToInt .Ptr .Usize ⟨0⟩,
        .Alloca .U8 none none, .Cast .PtrToInt .Ptr .Usize ⟨2⟩]
      bodyResultDests := [[⟨0⟩], [⟨1⟩], [⟨2⟩], [⟨3⟩]]
      terminator := .Return [⟨1⟩, ⟨3⟩] }
  else
    { params := []
      body := [.Alloca .U8 none none, .Cast .PtrToInt .Ptr .Usize ⟨0⟩]
      bodyResultDests := [[⟨0⟩], [⟨1⟩]]
      terminator := .Return [⟨1⟩] }

private def fixtureModule (model : ByteModel) (count : Nat)
    (globalFirst : Bool := false) : TrustIrEval.Module :=
  let declaration : Function :=
    { id := ⟨0⟩, name := "unused_declaration", ty := ⟨1⟩, entry := ⟨0⟩
      isDeclaration := true, blocks := .ok [] }
  let unsupportedBody :=
    { declaration with
      id := ⟨count - 3⟩, name := "unused_unsupported"
      isDeclaration := false, blocks := .error (.unsupported "inst.Unmodeled") }
  let unusedBody :=
    { declaration with
      id := ⟨count - 2⟩, name := "unused_body"
      isDeclaration := false
      blocks := .ok [(⟨0⟩, { params := [], body := [], terminator := .Return [] })] }
  let entry :=
    { declaration with
      id := entryId, name := "entry", ty := ⟨0⟩
      isDeclaration := false, blocks := .ok [(⟨0⟩, fixtureBlock globalFirst)] }
  { byteModel := .ok model
    functions := (List.range (count - 3)).map (fun i => { declaration with id := ⟨i⟩ }) ++
      [unsupportedBody, unusedBody, entry]
    funcTys := [
      { params := [], returns := if globalFirst then [.Usize, .Usize] else [.Usize]
        isVararg := false },
      { params := [], returns := [], isVararg := false }]
    globals := [{ ty := .U8, initializer := some (.int 7) }]
    enums := [], structs := [], types := [] }

private def okInts (model : ByteModel) (addresses : List Nat) : Json :=
  obj [("ok", Observation.renderGraphSpec (addresses.map (fun n =>
    .int model.pointerBits (Int.ofNat n))))]

private def initialAddress (model : ByteModel) (count : Nat) : Option Nat :=
  match initialStateForFunctionCount model count with
  | .ok state =>
    if state.memory.allocations.isEmpty && state.memory.nextAllocId == 0 then
      some state.memory.nextAddr
    else none
  | .error _ => none

private def isNamespaceRefusal (model : ByteModel) (count : Nat) : Bool :=
  match initialStateForFunctionCount model count with
  | .error (.typeError "function address namespace exceeds target pointer width") => true
  | _ => false

def main : IO Unit := do
  for model in [ByteModel.le32, .le64] do
    require "empty modules retain the allocation floor" (initialAddress model 0 == some 1024)
    let limit := model.addressLimit
    require "last representable first data address is accepted"
      (initialAddress model (limit - 2) == some (limit - 1))
    require "namespace exhaustion is a type error" (isNamespaceRefusal model (limit - 1))
    require "counts cannot wrap past the target width" (isNamespaceRefusal model limit)
    for count in [1023, 1024, 1101] do
      let module := fixtureModule model count
      require "count includes declarations and unused undecodable bodies"
        (module.functions.length == count)
      let expected := okInts model [max 1024 (count + 1)]
      let batch : Batch := { module := module, runs := [(entryId, []), (entryId, [])] }
      require s!"fresh allocation above all code addresses: {model.pointerBits}/{count}"
        (runBatch 3 3 .abort batch == .arr #[expected, expected])
      let context ← match contextOf module 3 with
        | .ok context => pure context
        | .error error => throw (IO.userError (reprStr error))
      require "direct runOne uses the same initialization"
        (runOne module context 3 .abort entryId [] == expected)
      let refused := initialStateForFunctionCount model (limit - 1)
      let refusal := renderError (.typeError "function address namespace exceeds target pointer width")
      require "namespace refusal precedes arguments and execution"
        (runOneWithInitialState module context refused 0 .abort entryId [.bool true] == refusal)
      require "namespace refusal precedes bodyless entry dispatch"
        (runOneWithInitialState module context refused 3 .abort ⟨0⟩ [] == refusal)
      require "missing entries remain a harness error"
        (runOneWithInitialState module context refused 3 .abort ⟨999999⟩ [] ==
          obj [("error", jstr "entry function 999999 is not in the module")])
    let module := fixtureModule model 1101 true
    let expected := okInts model [1104, 1105]
    require "global allocation aligns the reserved cursor before stack allocation"
      (runBatch 3 3 .abort { module := module, runs := [(entryId, [])] } == .arr #[expected])
  IO.println "Function namespace runner checks passed"
