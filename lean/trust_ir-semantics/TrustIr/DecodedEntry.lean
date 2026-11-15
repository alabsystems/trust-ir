-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
-- Pure production module-entry setup shared with the JSON oracle.
import TrustIr.DecodedContext

/-- Keep the original index-first enumeration under either standard API. -/
macro "trustIrEntryEnumFrom" : term => do
  if Lean.versionString == "4.8.0" then `(List.enumFrom)
  else if Lean.versionString == "4.30.0-rc2" then
    `(fun start values => (List.zipIdx values start).map Prod.swap)
  else Lean.Macro.throwError "unsupported compiler for entry enumeration"

namespace TrustIrEval
open TrustIr

/-- The first decode failure among the functions statically reachable from
    `root` (root included), or `none`. Bounded by the function count, so the
    walk terminates on a cyclic call graph. -/
def reachableDecodeFailure (m : Module) (root : FuncId) : Option DecodeError :=
  let lookup := fun (fid : FuncId) => m.functions.find? (fun f => f.id == fid)
  let rec go (fuel : Nat) (seen : List FuncId) (work : List FuncId) : Option DecodeError :=
    match fuel, work with
    | 0, _ => none
    | _, [] => none
    | fuel + 1, fid :: rest =>
      if seen.contains fid then go fuel seen rest
      else match lookup fid with
        | none => go fuel (fid :: seen) rest
        | some f =>
          match f.blocks with
          | .error e => some e
          | .ok blocks =>
            -- Amendment D: a drop is resolved against the WHOLE table, so a
            -- table row whose key did not decode makes every reachable drop
            -- unresolvable faithfully: refused before evaluation, never
            -- resolved against a partial table.
            if blocksDrop blocks && m.dropGlue.any (fun row => row.snd.isNone) then
              some (.unsupported "drop_glue.key")
            else go fuel (fid :: seen) (rest ++ calleesOf (dropGlueOf m) blocks)
  go (m.functions.length + 1) [] [root]

/-- The scalar entry bridge re-expresses valid pointer-sized carriers at the
    target width, preserving signed mathematics or unsigned raw value. Char
    Unicode validity remains the evaluator's UB check. The IPC omits
    nominal/signed carrier metadata, so this is not arbitrary malformed-
    carrier validation. -/
def targetScalarArgument (model : ByteModel) (ty : Ty) (value : Value) :
    Except SemError Value := do
  match ty, value with
  | .Usize, .int width raw =>
    let unsigned := truncateUnsigned raw width
    if unsigned < (2 : Int) ^ model.pointerBits then pure (Value.intAt model.pointerBits unsigned)
    else throw (.typeError "usize argument does not fit the target width")
  | .Isize, .int width raw =>
    let signed := toSigned raw width
    let half := (2 : Int) ^ (model.pointerBits - 1)
    if -half ≤ signed && signed < half then pure (Value.intAt model.pointerBits signed)
    else throw (.typeError "isize argument does not fit the target width")
  | _, _ => pure value

def targetScalarArguments (ctx : EvalContext) (types : List Ty) (args : List Value) :
    Except SemError (List Value) :=
  -- Leave arity errors to the original evaluator. Zipping must not erase an
  -- excess argument and turn a malformed call into a successful one.
  if types.length != args.length then pure args
  else (types.zip args).mapM (fun (ty, value) => targetScalarArgument ctx.byteModel ty value)

/-- Reserve the module-local code addresses `1 .. count` before any data
    allocation. Count every source function, including declarations and bodies
    the oracle cannot decode. This is module-entry initialization; callers of
    the pure evaluator still supply their own state. -/
def initialStateForFunctionCount (model : ByteModel) (count : Nat) :
    Except SemError MachineState :=
  if count + 1 < model.addressLimit then
    .ok { MachineState.empty with memory :=
      { Memory.empty with nextAddr := max 1024 (count + 1) } }
  else .error (.typeError "function address namespace exceeds target pointer width")

inductive EntryPreflightError where
  | decodeError (error : DecodeError)
  | semanticError (error : SemError)
  | missing
  | declared

inductive EntryPreflight where
  | blocked (error : EntryPreflightError)
  | ready (state : MachineState) (args : List Value)

/-- Original oracle preflight, in its original precedence order. Successful
argument normalization retains the original arity behavior. -/
def prepareDecodedEntry (m : Module) (ctx : EvalContext)
    (initialState : Except SemError MachineState) (fid : FuncId) (args : List Value) : EntryPreflight :=
  match reachableDecodeFailure m fid with
  | some error => .blocked (.decodeError error)
  | none =>
    match ctx.functions fid with
    | none =>
      if ctx.declared fid then
        match initialState with
        | .error error => .blocked (.semanticError error)
        | .ok _ => .blocked .declared
      else .blocked .missing
    | some function =>
      match initialState with
      | .error error => .blocked (.semanticError error)
      | .ok state =>
        match targetScalarArguments ctx function.body.paramTys args with
        | .error error => .blocked (.semanticError error)
        | .ok actualArgs => .ready state actualArgs

/-- Logical result before JSON presentation. Evaluated outcomes retain the
complete machine state even though the oracle renders only returned values. -/
inductive RunEntryResult where
  | decodeError (error : DecodeError)
  | missing
  | declared
  | evaluated (outcome : Except SemError (List Value × MachineState))

def EntryPreflightError.result : EntryPreflightError → RunEntryResult
  | .decodeError error => .decodeError error
  | .semanticError error => .evaluated (.error error)
  | .missing => .missing
  | .declared => .declared

def runPreparedEntry (ctx : EvalContext) (fuel : Nat) (strategy : PanicStrategy) (fid : FuncId) :
    EntryPreflight → RunEntryResult
  | .blocked error => error.result
  | .ready state args => .evaluated (Sem.run (evalFunctionInContext ctx fid args fuel strategy) state)

def runDecodedEntry (m : Module) (ctx : EvalContext) (initial : Except SemError MachineState)
    (fuel : Nat) (strategy : PanicStrategy) (fid : FuncId) (args : List Value) : RunEntryResult :=
  runPreparedEntry ctx fuel strategy fid (prepareDecodedEntry m ctx initial fid args)

/-- Apply one run's explicit choice tape to the cached initial state. -/
def withEntryChoices (initial : Except SemError MachineState) (choices : List Bool) :
    Except SemError MachineState :=
  initial.map (fun state => state.withFloatZeroChoices (FloatZeroChoiceTape.ofList choices))

/-- The actual batch entry state, including source function-address reservation
and this run's executable choice tape. -/
def moduleEntryState (m : Module) (ctx : EvalContext) (choices : List Bool) : Except SemError MachineState :=
  withEntryChoices (initialStateForFunctionCount ctx.byteModel m.functions.length) choices

/-- Single-entry form of actual source context assembly and oracle setup.
Batches can retain their once-prepared context and call runDecodedEntry. -/
def runDecodedModule (m : Module) (maxDepth : Nat) (choices : List Bool)
    (fuel : Nat) (strategy : PanicStrategy) (fid : FuncId) (args : List Value) : RunEntryResult :=
  match contextOf m maxDepth with
  | .error error => .decodeError error
  | .ok ctx => runDecodedEntry m ctx (moduleEntryState m ctx choices) fuel strategy fid args

/-- The original index-first ordering, specified independently of the API. -/
def entryIndexSpec {α : Type} (start : Nat) : List α → List (Nat × α)
  | [] => []
  | value :: rest => (start, value) :: entryIndexSpec (start + 1) rest

/-- Every entry retains its exact original position, for every list and offset. -/
theorem entryEnumFrom_eq_spec {α : Type} (start : Nat) (values : List α) :
    trustIrEntryEnumFrom start values = entryIndexSpec start values := by
  induction values generalizing start with
  | nil => rfl
  | cons value rest ih =>
    change (start, value) :: (trustIrEntryEnumFrom (start + 1) rest) =
      (start, value) :: entryIndexSpec (start + 1) rest
    exact congrArg (List.cons (start, value)) (ih (start + 1))

#trustIrAxiomsExact TrustIrEval.entryEnumFrom_eq_spec == []

/-- Production batch setup consumes each result immediately, so presentation
does not retain all completed machine states. Context/state setup happens once. -/
def runDecodedBatchWith {α : Type} (consume : FuncId → RunEntryResult → α)
    (m : Module) (runs : List (FuncId × List Value)) (choices : List (List Bool))
    (fuel depth : Nat) (strategy : PanicStrategy) : List α :=
  match contextOf m depth with
  | .error error => runs.map (fun (fid,_) => consume fid (.decodeError error))
  | .ok ctx =>
    let initial := initialStateForFunctionCount ctx.byteModel m.functions.length
    (trustIrEntryEnumFrom 0 runs).map (fun (index,(fid,args)) => consume fid
      (runDecodedEntry m ctx (withEntryChoices initial (choices.getD index [])) fuel strategy fid args))

/-- Retained raw logical results for proof consumers. The JSON production
runner instead consumes each result immediately with runDecodedBatchWith. -/
def runDecodedBatch (m : Module) (runs : List (FuncId × List Value)) (choices : List (List Bool))
    (fuel depth : Nat) (strategy : PanicStrategy) : List (FuncId × RunEntryResult) :=
  runDecodedBatchWith (fun fid result => (fid,result)) m runs choices fuel depth strategy

theorem runDecodedBatchWith_eq_map {α : Type} (consume : FuncId → RunEntryResult → α)
    (m : Module) (runs : List (FuncId × List Value)) (choices : List (List Bool))
    (fuel depth : Nat) (strategy : PanicStrategy) :
    runDecodedBatchWith consume m runs choices fuel depth strategy =
      (runDecodedBatch m runs choices fuel depth strategy).map (fun (fid,result) => consume fid result) := by
  unfold runDecodedBatch runDecodedBatchWith
  cases assembled : contextOf m depth <;> simp only [List.map_map,Function.comp_def]

end TrustIrEval
