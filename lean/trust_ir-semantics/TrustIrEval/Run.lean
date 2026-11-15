-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- The W5b oracle runner (roadmap WS2.19): assemble an `EvalContext` from a
-- decoded module, run `evalFunctionInContext` on each requested
-- (function, arguments) pair, and render the verdict as JSON.
--
-- Request: `{"fuel": n, "call_depth": n, "batches": [{"module": <serde
-- module>, "runs": [{"function": id, "args": [<scalar value>..]}..]}..]}`,
-- with an OPTIONAL top-level `"panic_strategy": "abort" | "unwind"`
-- (amendment D, Part 2; absent is `"abort"`, any other value refuses the
-- whole request).
-- Reply: one verdict list per batch, one verdict per run, in order.
--
-- Verdict grammar (one object per run):
--
--   {"ok": {"graph": {"version": 2, "nodes": [...], "roots": [...]}}}          the function returned these values
--   {"ub": "<detail>"}            undefined behaviour (`SemError.ub`)
--   {"panic": "<detail>"}         an `Assert` failed
--   {"unsupported": "<feature>"}  outside the executable subset, by NAME
--                                 (`UnsupportedFeature.code`, or the decoder's
--                                 `<kind>.<Variant>` for a construct with no
--                                 Lean mirror)
--   {"type_error": "<detail>"}    ill-formed IR by the model's lights — on a
--                                 validator-accepted module this is a
--                                 DISAGREEMENT the harness fails on
--   {"out_of_fuel": true}         block fuel or call depth exhausted
--   {"error": "<msg>"}            the module is not the serde schema (harness bug)
--
-- Value grammar (canonical, engine-neutral):
--
--   {"int": {"width": w, "raw": "<decimal>"}}   the value's w-bit two's-
--                                               complement bit pattern as an
--                                               unsigned decimal — the
--                                               interpreter's `InterpretInt::raw`
--   {"bool": b}
--   {"float": {"bits": "<decimal>"}}            binary64 bits (an F32 value is
--                                               exactly representable, so this
--                                               is bit-exact for every non-NaN)
--   {"float": "nan"}                            NaN-ness only (WS2.23 residue:
--                                               a NaN's payload is unobservable)
--   {"ptr": "null" | "nonnull"}                 addresses are engine-private;
--                                               only nullness is compared
--   {"fatptr": {"data": <value>, "metadata": <value>}}
--   {"aggregate": [..]} {"vector": [..]} {"sequence": [..]} {"set": [..]}
--   {"record": [[name, <value>]..]} {"closure": {"func": f, "captures": [..]}}
--   {"frame": n}                                a binding-frame handle (never
--                                               returned by a validated function)
--   {"poison": true}                            never reachable: the call boundary
--                                               refuses poison (`rejectPoisonValues`)

import TrustIrEval.Decode
import TrustIrEval.EnumAdmission
import TrustIr.DecodedEntry
import TrustIrEval.Observation

namespace TrustIrEval

open Lean (Json)
open TrustIr

-- ---------------------------------------------------------------------------
-- Context assembly
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Argument decoding (the harness's canonical scalar and thin-pointer grammar)
-- ---------------------------------------------------------------------------

def argValue (j : Json) : D Value := do
  let (tag, p) ← tagged "arg" j
  match tag with
  | "int" =>
    let width ← natField p "width"
    let raw ← wideInt "raw" (← field p "raw")
    if raw < 0 || raw ≥ (2 : Int) ^ width then
      malformed s!"int argument outside its {width}-bit range"
    else pure (.int width raw)
  | "bool" => pure (.bool (← bool "bool" p))
  | "null_ptr" =>
    if ← bool "null_ptr" p then pure .nullPtr
    else malformed "null_ptr argument must be true"
  | "dangling_ptr" =>
    let address ← wideInt "dangling_ptr" p
    if address < 0 || address > word64Max then
      malformed "dangling_ptr argument outside u64"
    else pure (.ptr address.toNat none)
  | other => unsupported s!"arg.{other}"

-- ---------------------------------------------------------------------------
-- Value rendering
-- ---------------------------------------------------------------------------

def jstr (s : String) : Json := .str s
def jnat (n : Nat) : Json := .num n
def obj (kvs : List (String × Json)) : Json := Json.mkObj kvs

-- ---------------------------------------------------------------------------
-- Running
-- ---------------------------------------------------------------------------

/-- A resolved panic site: `{"entry": E, "location": {"global": G, "offset":
    O} | "other"}`. -/
def renderPanicSite (site : PanicOutcomeSite) : Json :=
  let loc := match site.loc with
    | .global g offset => obj [("global", jnat g.index), ("offset", jnat offset)]
    | .other => jstr "other"
  obj [("entry", jnat site.entry.index), ("location", loc)]

def renderError : SemError → Json
  | .ub msg => obj [("ub", jstr msg)]
  -- Amendment P (wire v54): a sited panic also names its entry and resolved
  -- location; an unsited one renders exactly as before.
  | .panic msg none => obj [("panic", jstr msg)]
  | .panic msg (some site) => obj [("panic", jstr msg), ("site", renderPanicSite site)]
  | .typeError msg => obj [("type_error", jstr msg)]
  | .unsupported feature msg =>
    obj [("unsupported", jstr feature.code), ("detail", jstr msg)]
  | .outOfFuel => obj [("out_of_fuel", .bool true)]
  | .outOfMemory msg => obj [("out_of_memory", jstr msg)]
  -- Unreachable: `evalFunctionInContext` reports an unwinding that escapes
  -- the entry as the panic its raise recorded. Rendered as a harness error,
  -- never as a verdict, should it ever surface.
  | .unwinding _ _ => obj [("error", jstr "unwinding escaped the entry")]

def renderDecodeError : DecodeError → Json
  | .unsupported feature => obj [("unsupported", jstr feature)]
  | .malformed msg => obj [("error", jstr msg)]

/-- Render the shared logical result without retaining its completed machine state. -/
def renderRunEntryResult (fid : FuncId) : RunEntryResult → Json
  | .decodeError error => renderDecodeError error
  | .missing => obj [("error", jstr s!"entry function {fid.index} is not in the module")]
  | .declared => obj [("unsupported", jstr "interprocedural_call"),
      ("detail", jstr "entry function is a bodyless declaration")]
  | .evaluated (.error error) => renderError error
  | .evaluated (.ok (values,_)) => obj [("ok", Observation.renderGraph values)]

/-- Run one request with the module's precomputed fresh initial state. A call
    to a function the context has
    no body for is the interpreter's `UnsupportedCall` (a bodyless
    declaration is not executable in-format, WS2.12); the evaluator spells
    it `Call: undefined function`, a type error, so the ENTRY case is
    classified here before evaluation — a nested call to a declaration is
    reclassified by `stepNWithContext`'s own arm. -/
def runOneWithInitialState (m : Module) (ctx : EvalContext)
    (initialState : Except SemError MachineState) (fuel : Nat) (strat : PanicStrategy)
    (fid : FuncId) (args : List Value) : Json :=
  renderRunEntryResult fid (runDecodedEntry m ctx initialState fuel strat fid args)

/-- The shared pure setup and rendering preserve the original oracle's exact
branch order and JSON result, for arbitrary decoded modules and initial errors. -/
theorem runOneWithInitialState_eq_original (m : Module) (ctx : EvalContext)
    (initialState : Except SemError MachineState) (fuel : Nat) (strat : PanicStrategy)
    (fid : FuncId) (args : List Value) :
    runOneWithInitialState m ctx initialState fuel strat fid args = (
match reachableDecodeFailure m fid with
  | some e => renderDecodeError e
  | none =>
    match ctx.functions fid with
    | none =>
      -- Only a DECLARED entry is a named refusal; an id the module does not
      -- define at all is a harness bug, never coverage.
      if ctx.declared fid then
        match initialState with
        | .error e => renderError e
        | .ok _ =>
          obj [("unsupported", jstr "interprocedural_call"),
               ("detail", jstr "entry function is a bodyless declaration")]
      else obj [("error", jstr s!"entry function {fid.index} is not in the module")]
    | some func =>
      match initialState with
      | .error e => renderError e
      | .ok state =>
        match targetScalarArguments ctx func.body.paramTys args with
        | .error e => renderError e
        | .ok args =>
          match Sem.run (evalFunctionInContext ctx fid args fuel strat) state with
          | .ok (values, _) => obj [("ok", Observation.renderGraph values)]
          | .error e => renderError e) := by
  unfold runOneWithInitialState runDecodedEntry prepareDecodedEntry
  repeat' first
    | (solve | simp_all [runPreparedEntry,renderRunEntryResult,EntryPreflightError.result])
    | split

/-- Run one request, reserving all source function addresses before data. -/
def runOne (m : Module) (ctx : EvalContext) (fuel : Nat) (strat : PanicStrategy)
    (fid : FuncId) (args : List Value) : Json :=
  runOneWithInitialState m ctx
    (initialStateForFunctionCount ctx.byteModel m.functions.length) fuel strat fid args

/-- One module and the runs over it. -/
structure Batch where
  module : Module
  runs : List (FuncId × List Value)
  /-- Per-run executable choice witnesses; missing rows select the empty prefix. -/
  floatZeroChoices : List (List Bool) := []

structure Request where
  fuel : Nat
  callDepth : Nat
  strategy : PanicStrategy
  batches : List Batch

/-- The optional `"panic_strategy"` (amendment D, Part 2): absent is
    `.abort`; only `"abort"` and `"unwind"` are accepted. -/
def panicStrategyField (j : Json) : D PanicStrategy :=
  match j.getObjVal? "panic_strategy" with
  | .error _ => pure .abort
  | .ok (.str "abort") => pure .abort
  | .ok (.str "unwind") => pure .unwind
  | .ok other => malformed s!"panic_strategy: expected \"abort\" or \"unwind\", got {other.compress}"

def batch (j : Json) : D Batch := do
  let rows ← listField j "runs"
  let runs ← rows.mapM (fun r => do
    pure (← funcId "function" (← field r "function"),
          ← (← listField r "args").mapM argValue))
  let choices ← rows.mapM (fun r => do
    match r.getObjVal? "float_zero_choices" with
    | .error _ => pure []
    | .ok value =>
      (← arr "float_zero_choices" value).mapM (fun item =>
        match item with
        | .bool value => pure value
        | _ => malformed "float_zero_choices: expected Boolean entries"))
  pure { module := ← module (← field j "module"), runs := runs, floatZeroChoices := choices }

def request (j : Json) : D Request := do
  pure { fuel := ← natField j "fuel"
         callDepth := ← natField j "call_depth"
         strategy := ← panicStrategyField j
         batches := ← (← listField j "batches").mapM batch }

/-- One batch: one verdict per run, in request order. A context-assembly
    refusal is rendered for every requested run. Per-function decode and
    metadata failures keep their original lazy lookup/preflight treatment. -/
def runBatch (fuel callDepth : Nat) (strat : PanicStrategy) (b : Batch) : Json :=
  .arr (runDecodedBatchWith renderRunEntryResult b.module b.runs b.floatZeroChoices fuel callDepth strat).toArray

/-- Batch factoring preserves once-prepared context/state, order and tapes. -/
theorem runBatch_eq_original (fuel callDepth : Nat) (strat : PanicStrategy) (b : Batch) :
    runBatch fuel callDepth strat b = (
match contextOf b.module callDepth with
  | .error e => .arr (b.runs.map (fun _ => renderDecodeError e)).toArray
  | .ok ctx =>
    let initialState := initialStateForFunctionCount ctx.byteModel b.module.functions.length
    .arr ((trustIrEntryEnumFrom 0 b.runs).map (fun (index, (fid, args)) =>
      let choices := FloatZeroChoiceTape.ofList (b.floatZeroChoices.getD index [])
      let state := initialState.map (fun state => state.withFloatZeroChoices choices)
      runOneWithInitialState b.module ctx state fuel strat fid args)).toArray) := by
  unfold runBatch runDecodedBatchWith
  cases assembled : contextOf b.module callDepth <;>
    simp only [assembled,List.map_map,Function.comp_def]
  · rfl
  · rfl

-- ---------------------------------------------------------------------------
-- Amendment S: the substitution differential
-- (`crates/trust-ir-conformance/tests/template_subst_differential.rs`).
--
-- Request: `{"template_subst": [{"ty": <TyG<TemplateRef>>, "params": [<Ty> |
-- null..], "holes": [<Ty> | null..], "expected": <Ty> | null}..]}` — a level-S
-- type, the images of its parameters and holes by index (`null`, or past the
-- end: no image), and the level-R type Rust's substitution produced (`null`:
-- Rust found a name with no image).
-- Reply: one verdict per case, in order: `{"agree": true}`,
-- `{"mismatch": "<Lean's result>"}`, `{"unsupported": ..}` or `{"error": ..}`.
-- ---------------------------------------------------------------------------

/-- One case: Lean's `substTy` against Rust's result. -/
def substCase (j : Json) : D Json := do
  let t ← templateTy (← field j "ty")
  let params ← (← listField j "params").mapM (fun x => optional x ty)
  let holes ← (← listField j "holes").mapM (fun x => optional x ty)
  let expected ← optional (← field j "expected") ty
  let got := substTy (fun i => (trustIrListGet? params i).bind id) (fun h => (trustIrListGet? holes h).bind id) t
  if got == expected then
    pure (obj [("agree", .bool true)])
  else
    pure (obj [("mismatch", jstr s!"{repr got}")])

/-- Every case of a substitution request, in order. -/
def runTemplateSubst (cases : List Json) : Json :=
  .arr (cases.map (fun c => match substCase c with
    | .ok verdict => verdict
    | .error e => renderDecodeError e)).toArray

/-- ID-only declaration admission for actual serialized modules. -/
def runEnumAdmission (documents : List Json) : Json :=
  .arr (documents.map (fun document => match enumAdmission document with
    | .ok admitted => obj [("enum_ids_admitted", .bool admitted)]
    | .error error => renderDecodeError error)).toArray

/-- The whole request: one verdict list per batch, in request order, or a
    single `{"error": ..}` object when the request itself is not the schema
    (the harness treats a non-array reply as a broken oracle). A request
    carrying `template_subst` is the substitution differential instead.
    `enum_id_admission` rechecks only distinct u32 enum IDs on original modules. -/
def runRequest (j : Json) : Json :=
  match j.getObjVal? "template_subst" with
  | .ok (.arr cases) => runTemplateSubst cases.toList
  | _ =>
    match j.getObjVal? "enum_id_admission" with
    | .ok (.arr documents) => runEnumAdmission documents.toList
    | .ok _ => renderDecodeError (.malformed "enum_id_admission: expected array")
    | .error _ =>
      match request j with
      | .error e => renderDecodeError e
      | .ok req => .arr (req.batches.map (runBatch req.fuel req.callDepth req.strategy)).toArray

/-- Every request without the new key retains the exact original dispatcher. -/
theorem runRequest_without_enum_admission (document : Json) (error : String)
    (absent : document.getObjVal? "enum_id_admission" = .error error) :
    runRequest document =
      (match document.getObjVal? "template_subst" with
      | .ok (.arr cases) => runTemplateSubst cases.toList
      | _ => match request document with
        | .error failure => renderDecodeError failure
        | .ok req => .arr (req.batches.map (runBatch req.fuel req.callDepth req.strategy)).toArray) := by
  unfold runRequest
  cases template : document.getObjVal? "template_subst" with
  | error _ => simp [template, absent]
  | ok value => cases value <;> simp [template, absent]

theorem runRequest_enum_admission (document : Json) (documents : Array Json) (error : String)
    (noTemplate : document.getObjVal? "template_subst" = .error error)
    (admitted : document.getObjVal? "enum_id_admission" = .ok (.arr documents)) :
    runRequest document = runEnumAdmission documents.toList := by
  simp [runRequest, noTemplate, admitted]

end TrustIrEval

/- Original legacy printer assertion, preserved verbatim:
/-- info: 'TrustIrEval.runOneWithInitialState_eq_original' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.runOneWithInitialState_eq_original
-/
#trustIrAxiomsExact TrustIrEval.runOneWithInitialState_eq_original == [propext, Quot.sound, Classical.choice]

/- Original legacy printer assertion, preserved verbatim:
/-- info: 'TrustIrEval.runBatch_eq_original' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.runBatch_eq_original
-/
#trustIrAxiomsExact TrustIrEval.runBatch_eq_original == [propext, Quot.sound, Classical.choice]

/- Original legacy printer assertion, preserved verbatim:
/-- info: 'TrustIrEval.runRequest_without_enum_admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.runRequest_without_enum_admission
-/
#trustIrAxiomsExact TrustIrEval.runRequest_without_enum_admission == [propext, Classical.choice, Quot.sound]

/- Original legacy printer assertion, preserved verbatim:
/-- info: 'TrustIrEval.runRequest_enum_admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.runRequest_enum_admission
-/
#trustIrAxiomsExact TrustIrEval.runRequest_enum_admission == [propext, Classical.choice, Quot.sound]
