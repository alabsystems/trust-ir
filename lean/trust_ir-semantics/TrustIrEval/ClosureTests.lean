-- Copyright 2026 Andrew Yates | Author: Andrew Yates | Apache-2.0
-- Executable regression controls, not proof certificates.
import TrustIrRuntime
import TrustIrEval.Run
open TrustIr TrustIrEval Lean

private def vid (n : Nat) : ValueId := ⟨n⟩
private def fid (n : Nat) : FuncId := ⟨n⟩
private def bid (n : Nat) : BlockId := ⟨n⟩
private def cid : ClosureTyId := ⟨0⟩
private def sig : FuncTyId := ⟨0⟩
private def block (params : List (ValueId × Ty)) (body : List Inst)
    (dests : List (List ValueId)) (term : Inst) : BasicBlock :=
  { params := params, body := body, bodyResultDests := dests, terminator := term }
private def fn (params returns : List Ty) (b : BasicBlock) : EvalFunction :=
  { body := { paramTys := params, returnTys := returns }
    cfg := fun pc => if pc == bid 0 then some b else none
    entryBlock := bid 0, callingConv := .Rust }
private def target : EvalFunction := fn [.Ptr, .I64] [.Ptr]
  (block [(vid 0,.Ptr),(vid 1,.I64)] [.Store .I64 (vid 0) (vid 1) false none] [[]]
    (.Return [vid 0]))
private def entry : EvalFunction := fn [] [.I64,.I64]
  (block []
    [.Alloca .I64 none none, .Alloca .I64 none none,
     .MakeClosure cid (fid 1) [vid 0],
     .InsertField (.Closure cid) (vid 2) 0 (vid 1),
     .Const .I64 (.int 3), .Const .I64 (.int 9),
     .CallIndirect (vid 2) sig [vid 4] .Rust,
     .CallIndirect (vid 3) sig [vid 5] .Rust,
     .Load .I64 (vid 6) false none,
     .Load .I64 (vid 7) false none]
    [[vid 0],[vid 1],[vid 2],[vid 3],[vid 4],[vid 5],[vid 6],[vid 7],[vid 8],[vid 9]]
    (.Return [vid 8, vid 9]))
private def ctx : EvalContext :=
  { EvalContext.empty with
    maxCallDepth := 8
    closures := fun c => if c == cid then some {func := sig,captures := [.Ptr]} else none
    funcTys := fun s => if s == sig then some {params := [.I64],returns := [.Ptr],isVararg := false} else none
    functions := fun f => if f == fid 0 then some entry else if f == fid 1 then some target else none }
private def require (name : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError name)
  IO.println s!"PASS {name}"
private def isError {α : Type} : Except SemError α → Bool
  | .error _ => true | _ => false
private def errCode {α : Type} : Except SemError α → String
  | .error e => e.code | .ok _ => "ok"
private def intPair : Except SemError (List Value × MachineState) → Bool
  | .ok ([.int 64 3,.int 64 9], _) => true | _ => false
private def pointer : Value := .ptr 24 (some ⟨7⟩)
private def returnsPointer : Except SemError Value → Bool
  | .ok (.ptr 24 (some ⟨7⟩)) => true | _ => false
private def keepsPointer : Except SemError Value → Bool
  | .ok (.typedClosure ⟨0⟩ ⟨1⟩ [.ptr 24 (some ⟨7⟩)]) => true | _ => false


private def serdeClosureFixture : String := r##"{"functions":[{"id":0,"name":"decoded_host","ty":1,"entry":0,"calling_conv":"Rust","blocks":[{"id":0,"params":[[0,"I64"]],"body":[{"inst":{"MakeClosure":{"ty":0,"func":1,"captures":[0]}},"results":[1]},{"inst":{"CallIndirect":{"callee":1,"sig":0,"args":[],"calling_conv":"Rust"}},"results":[2]},{"inst":{"Return":{"values":[2]}},"results":[]}]}]},{"id":1,"name":"decoded_target","ty":1,"entry":0,"calling_conv":"Rust","blocks":[{"id":0,"params":[[0,"I64"]],"body":[{"inst":{"Return":{"values":[0]}},"results":[]}]}]}],"func_types":[{"params":[],"returns":["I64"],"is_vararg":false},{"params":["I64"],"returns":["I64"],"is_vararg":false}],"closure_types":[{"func":0,"captures":["I64"]}],"globals":[],"enums":[],"structs":[],"types":[]}"##

private def decodedClosure (text : String) : IO (TrustIrEval.Module × EvalContext) := do
  let json ← match Json.parse text with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let module ← match TrustIrEval.module json with
    | .ok value => pure value
    | .error error => throw (IO.userError (reprStr error))
  let context ← match contextOf module 2 with
    | .ok value => pure value
    | .error error => throw (IO.userError (reprStr error))
  pure (module, context)

private def decoderControls : IO Unit := do
  let (module, context) ← decodedClosure serdeClosureFixture
  require "decoder retains the actual nominal closure table"
    (match module.closureTys, context.closures cid with
      | [{func := ⟨0⟩, captures := [.I64]}], some {func := ⟨0⟩, captures := [.I64]} => true
      | _, _ => false)
  require "decoded MakeClosure and CallIndirect execute with the recorded convention"
    (match Sem.run (evalFunctionInContext context (fid 0) [.int 64 7] 3) MachineState.empty with
      | .ok ([.int 64 7], _) => true
      | _ => false)
  let (_, wrongConvention) ← decodedClosure (serdeClosureFixture.replace
    "\"name\":\"decoded_target\",\"ty\":1,\"entry\":0,\"calling_conv\":\"Rust\""
    "\"name\":\"decoded_target\",\"ty\":1,\"entry\":0,\"calling_conv\":\"C\"")
  require "decoder convention mismatch remains a rejected call"
    (isError (Sem.run (evalFunctionInContext wrongConvention (fid 0) [.int 64 7] 3) MachineState.empty))
  let (_, wrongCaptures) ← decodedClosure (serdeClosureFixture.replace
    "\"closure_types\":[{\"func\":0,\"captures\":[\"I64\"]}]"
    "\"closure_types\":[{\"func\":0,\"captures\":[\"Bool\"]}]")
  require "decoder capture table mismatch cannot be guessed from values"
    (isError (Sem.run (evalFunctionInContext wrongCaptures (fid 0) [.int 64 7] 3) MachineState.empty))
  let (_, noCaptures) ← decodedClosure (serdeClosureFixture.replace
    "\"closure_types\":[{\"func\":0,\"captures\":[\"I64\"]}]"
    "\"closure_types\":[]")
  require "decoder missing nominal closure row stays refused"
    (errCode (Sem.run (evalFunctionInContext noCaptures (fid 0) [.int 64 7] 3) MachineState.empty) == "unsupported.closure_def_table")

def main : IO Unit := do
  decoderControls
  require "two immutable environments call with live pointers and retain effects"
    (intPair (Sem.run (evalFunctionInContext ctx (fid 0) [] 10) MachineState.empty))
  require "construction retains allocation provenance"
    (keepsPointer (makeClosureValue ctx cid (fid 1) [pointer]))
  require "capture extraction returns same pointer"
    (returnsPointer (closureExtract ctx .Ptr cid (fid 1) [pointer] 0))
  let constCtx := {ctx with
    functions := fun _ => none
    closures := fun _ => some {func := sig, captures := [.I64]}}
  require "unused legacy closure target is not invoked by constant construction"
    (match constValueAtWithDefs constCtx
        (.Closure cid) (.closure (fid 1) [.int 24]) with
      | .ok (.typedClosure _ _ [.int 64 24]) => true
      | _ => false)
  require "capture extraction does not apply the target"
    (returnsPointer (closureExtract {ctx with functions := fun _ => none} .Ptr cid (fid 1) [pointer] 0))
  require "capture update does not apply the target"
    (keepsPointer (closureInsert {ctx with functions := fun _ => none} (.Closure cid) cid (fid 1) [pointer] 0 pointer))
  require "nominal type mismatch rejected"
    (isError (closureInsert ctx (.Closure ⟨1⟩) cid (fid 1) [pointer] 0 pointer))
  require "update rejects wrong capture type"
    (isError (closureInsert ctx (.Closure cid) cid (fid 1) [pointer] 0 (.int 64 0)))
  require "extract rejects wrong access type"
    (isError (closureExtract ctx .I64 cid (fid 1) [pointer] 0))
  require "out of bounds rejected"
    (errCode (closureInsert ctx (.Closure cid) cid (fid 1) [pointer] 1 pointer) == "ub")
  require "poison capture rejected"
    (errCode (makeClosureValue ctx cid (fid 1) [.undef .Ptr]) == "ub")
  require "missing closure table refuses"
    (errCode (makeClosureValue {ctx with closures := fun _ => none} cid (fid 1) [pointer]) == "unsupported.closure_def_table")
  require "missing target rejected"
    (isError (makeClosureValue ctx cid (fid 9) [pointer]))
  require "bodyless target refuses"
    (errCode (makeClosureValue {ctx with declared := fun _ => true} cid (fid 9) [pointer]) == "unsupported.interprocedural_call")
  require "wrong physical signature rejected"
    (isError (makeClosureValue {ctx with functions := fun _ => some {target with body := {target.body with paramTys := [.I64,.Ptr]}}} cid (fid 1) [pointer]))
  require "physical vararg rejected"
    (isError (makeClosureValue {ctx with functions := fun _ => some {target with body := {target.body with isVararg := true}}} cid (fid 1) [pointer]))
  require "apparent vararg rejected"
    (isError (makeClosureValue {ctx with funcTys := fun _ => some {params := [.I64],returns := [.Ptr],isVararg := true}} cid (fid 1) [pointer]))
  require "same-shape different signature id rejected"
    (isError (closureCall {ctx with funcTys := fun _ => some {params := [.I64],returns := [.Ptr],isVararg := false}} cid (fid 1) [pointer] ⟨1⟩ [.int 64 3] .Rust))
  require "calling convention mismatch rejected"
    (isError (closureCall ctx cid (fid 1) [pointer] sig [.int 64 3] .C))
  require "wrong apparent argument rejected"
    (isError (closureCall ctx cid (fid 1) [pointer] sig [.bool true] .Rust))
  require "wrong argument arity rejected"
    (isError (closureCall ctx cid (fid 1) [pointer] sig [] .Rust))
  require "bare MakeClosure preserves context refusal"
    (errCode (Sem.run (stepInst (.MakeClosure cid (fid 1) []) .le64) MachineState.empty) == "unsupported.closure_def_table")
  require "zero call depth refuses before closure target dispatch"
    (errCode (Sem.run (evalFunctionInContext {ctx with maxCallDepth := 0} (fid 0) [] 10) MachineState.empty) == "out_of_fuel")
  let tail := fn [.Closure cid,.I64] [.Ptr]
    (block [(vid 0,.Closure cid),(vid 1,.I64)] [] [] (.CallIndirect (vid 0) sig [vid 1] .Rust))
  let tailCtx := {ctx with functions := fun f => if f == fid 2 then some tail else ctx.functions f}
  let (base, memory) := Memory.empty.alloc 8 8 0 .rustStack
  let st : MachineState := { MachineState.empty with
    memory := memory
    permissions := PermissionMap.empty.set ⟨0⟩ .owned }
  let tailValue := .typedClosure cid (fid 1) [.ptr base (some ⟨0⟩)]
  let result := Sem.run (evalFunctionInContext tailCtx (fid 2) [tailValue,.int 64 41] 10) st
  require "terminator closure call returns original pointer and persists store" (match result with
    | .ok ([.ptr address (some ⟨0⟩)], final) =>
      address == base && final.memory.readBytes base 8 == some (encodeIntBytes 41 8)
    | _ => false)
  let badReturn := {target with cfg := fun _ => some (block [(vid 0,.Ptr),(vid 1,.I64)]
    [.Const .Bool (.bool true)] [[vid 2]] (.Return [vid 2]))}
  require "bad physical return value rejected" (isError (Sem.run
    (evalFunctionInContext {tailCtx with functions := fun f => if f == fid 1 then some badReturn else tailCtx.functions f}
      (fid 2) [tailValue,.int 64 41] 10) st))
  let poisonTarget := {target with cfg := fun _ => some (block [(vid 0,.Ptr),(vid 1,.I64)]
    [.Const .Bool (.bool false), .Assert (vid 2) .Unspecified none] [[vid 2],[]] (.Return [vid 0]))}
  require "callee panic remains panic" (errCode (Sem.run
    (evalFunctionInContext {tailCtx with functions := fun f => if f == fid 1 then some poisonTarget else tailCtx.functions f}
      (fid 2) [tailValue,.int 64 41] 10) st) == "panic")
