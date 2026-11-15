-- Copyright 2026 Andrew Yates | Author: Andrew Yates | Apache-2.0
-- Executable controls; forged values/tables here do not claim module validity.
-- Run: lake env lean --run TrustIrEval/FunctionMemoryTests.lean
import TrustIrRuntime
import TrustIrEval.Run

open TrustIr TrustIrEval

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def errorIs {α : Type} (code : String) (result : Except SemError α) : Bool :=
  match result with
  | .error error => error.code == code
  | .ok _ => false

private def bytesAre (result : Except SemError (List UInt8)) (expected : List UInt8) : Bool :=
  match result with
  | .ok bytes => bytes == expected
  | .error _ => false

private def isFunction (result : Except SemError Value) (signature target : Nat) : Bool :=
  match result with
  | .ok (.fnDef held function) => held.index == signature && function.index == target
  | _ => false

private def isNull (result : Except SemError Value) : Bool :=
  match result with | .ok .nullPtr => true | _ => false

private def hasValue (state : MachineState) (id : ValueId) (expected : Value) : Bool :=
  match state.lookupValue id with
  | some value => Observation.renderGraphSpec [value] == Observation.renderGraphSpec [expected]
  | none => false

private def order : FunctionAddressOrder := some [⟨42⟩, ⟨4294967295⟩, ⟨7⟩, ⟨3⟩]
private def signature : FuncTyId := ⟨5⟩
private def code : Value := .fnDef signature ⟨4294967295⟩

private def context (model : ByteModel) : EvalContext :=
  { EvalContext.empty with byteModel := model, functionOrder := order }

private def slotState (model : ByteModel) (bytes : List UInt8) : MachineState :=
  let (base, memory) := Memory.empty.alloc model.pointerBytes model.pointerBytes 0 .rustStack
  { MachineState.empty with
    memory := memory.writeBytes base bytes
    permissions := PermissionMap.empty.set ⟨0⟩ .owned
    locals := ValueMap.empty.set ⟨0⟩ (.ptr base (some ⟨0⟩))
      |>.set ⟨1⟩ code |>.set ⟨2⟩ (.fnDef signature ⟨7⟩)
    nextValueId := 3 }

private def nullCall (model : ByteModel) (body : Bool) (invoke : Bool) :
    Except SemError (List Value × MachineState) :=
  let call := if invoke then
      Inst.InvokeIndirect ⟨0⟩ signature [] .C ⟨1⟩ [] ⟨2⟩
    else .CallIndirect ⟨0⟩ signature [] .C
  let block : BasicBlock :=
    if body then
      { params := [], body := [.NullPtr, call], bodyResultDests := [[⟨0⟩], []]
        terminator := .Return [] }
    else
      { params := [], body := [.NullPtr], bodyResultDests := [[⟨0⟩]], terminator := call }
  let cfg : CFG := fun _ => some block
  Sem.run (stepNWithContext (context model) 1 0 cfg ⟨0⟩ []) MachineState.empty

def main : IO Unit := do
  for model in [ByteModel.le32, .le64] do
    let word := encodeIntBytes 2 model.pointerBytes
    let encode := encodeMemoryWithFunctions model order (.Func signature)
    let decode := decodeMemoryWithFunctions model order Memory.empty (.Func signature)
    require "sparse identity uses source position two" (bytesAre (encode code) word)
    require "load recovers identity without an executable body" (isFunction (decode word) 5 4294967295)
    require "load type supplies the signature"
      (isFunction (decodeMemoryWithFunctions model order Memory.empty (.Func ⟨8⟩) word) 8 4294967295)
    require "unknown identity is a type error"
      (errorIs "type_error" (encode (.fnDef signature ⟨99⟩)))
    require "static and held signature must agree"
      (errorIs "type_error" (encode (.fnDef ⟨6⟩ ⟨4294967295⟩)))
    require "no table cannot invent a nonzero code image"
      (errorIs "unsupported.layout" (encodeMemoryWithFunctions model none (.Func signature) code))
    require "unknown nonzero word is a type error"
      (errorIs "type_error" (decode (encodeIntBytes 999999 model.pointerBytes)))
    require "an empty module registers no nonzero word"
      (errorIs "type_error" (decodeMemoryWithFunctions model (some []) Memory.empty
        (.Func signature) word))
    require "wrong image length is a type error" (errorIs "type_error" (decode []))
    let zeros := List.replicate model.pointerBytes 0
    require "null stores a zero word without module lookup"
      (bytesAre (encodeMemoryWithFunctions model none (.Func signature) .nullPtr) zeros)
    require "null loads without module lookup"
      (isNull (decodeMemoryWithFunctions model none Memory.empty (.Func signature) zeros))
    require "last target word fits"
      (match checkedFunctionAddress model (model.addressLimit - 2) with
       | .ok address => address == model.addressLimit - 1 | _ => false)
    require "code address overflow cannot wrap"
      (errorIs "type_error" (checkedFunctionAddress model (model.addressLimit - 1)))
    for body in [false, true] do
      require "null calls fail before depth exhaustion" (errorIs "type_error" (nullCall model body false))
    require "null invoke fails before depth exhaustion" (errorIs "type_error" (nullCall model false true))
    let ctx := context model
    require "function Undef is UB even when never inspected"
      (errorIs "ub" (Sem.run (stepInstWithContext ctx (.Undef (.Func signature))) MachineState.empty))
    let state := slotState model word
    let load : Sem Value := do
      let result ← stepInstWithContext ctx (.Load (.Func signature) ⟨0⟩ false none)
      match result with
      | .value (some id) => Sem.lookupValue id
      | _ => Sem.throwTypeError "load did not bind a value"
    require "actual contextual load recovers the function"
      (match Sem.run load state with
       | .ok (.fnDef held target, _) => held.index == 5 && target.index == 4294967295
       | _ => false)
    for strict in [false, true] do
      require "uninitialized function words are never partial scalar loads"
        (errorIs "ub" (Sem.run (stepInstWithContext ctx
          (.Load (.Func signature) ⟨0⟩ strict none)) (slotState model [])))
    let exchange := stepInstWithContext ctx
      (.CmpXchg (.Func signature) ⟨0⟩ ⟨1⟩ ⟨2⟩ .SeqCst .SeqCst false)
    require "strong exchange uses FnDef identity and writes the new source word"
      (match Sem.run exchange state with
       | .ok (.values [old, flag], final) =>
         hasValue final flag (.bool true) && hasValue final old code
           && final.memory.readBytes 1024 model.pointerBytes ==
             some (encodeIntBytes 3 model.pointerBytes)
       | _ => false)
    require "weak exchange remains refused before operand lookup"
      (errorIs "unsupported.weak_cmpxchg" (Sem.run (stepInstWithContext ctx
        (.CmpXchg (.Func signature) ⟨99⟩ ⟨100⟩ ⟨101⟩ .SeqCst .SeqCst true)) MachineState.empty))
    require "aggregate byte layout remains outside this leaf tranche"
      (errorIs "unsupported.layout" (Sem.run (stepInstWithContext ctx
        (.Alloca (.Tuple [.Func signature, .Ptr]) none none)) MachineState.empty))
  IO.println "Function leaf-memory runtime checks passed"
