-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- The WHOLE-ENVIRONMENT axiom census and kernel replay behind the
-- `lean-proofs` standing gate (scripts/lean_proofs.py, gate 14 of
-- scripts/ci_gates.sh).
--
-- `TrustIr/Proofs/AxiomAudit.lean` pins the axiom printout of a CURATED list
-- of theorems with `#guard_msgs`. A theorem that is not on that list can rest
-- on a proof placeholder, on `native_decide` (`Lean.ofReduceBool`) or on a
-- fresh axiom, and the build stays green: a placeholder only WARNS. This file
-- closes that gap for everything that enters the environment. It imports the
-- `TrustIr` library (the package's default target, which the gate builds just
-- before with `lake build TrustIr`) and, for EVERY SAFE constant declared in
-- a `TrustIr.*` module (theorems, definitions, instances, and the auxiliary
-- `_proof_` / `match_` / `_eq_` constants the elaborator adds), collects the
-- axioms its kernel term depends on. It then refuses:
--
--   * any axiom outside `allowedAxioms` (the Lean-core trio plus the one
--     documented first-party boundary `TrustIr.ay_sound_unsat`). A proof
--     placeholder surfaces here as `sorryAx`; `native_decide` surfaces as
--     `Lean.ofReduceBool`, which is admitted ONLY in `nativeDecideModules`;
--   * any safe `axiom` DECLARED in a `TrustIr.*` module other than
--     `TrustIr.ay_sound_unsat`, apart from the modern compiled fixture assertions
--     described below, whether or not anything uses it yet, and the
--     absence of that one (the boundary moved: update TRUST.md item 2 too);
--   * an empty census: nothing imported is not a pass.
--
-- Each refusal names the declaration and the axiom, and marks the
-- declarations whose OWN term names the axiom (`direct`) apart from those that
-- inherit it. Unsafe constants (the compiler's `_cstage` / `_spec` /
-- `_elambda` artifacts, 12k definitions and 482 "axioms" at the time of
-- writing) are out of scope by construction: the kernel refuses a safe
-- declaration that names an unsafe one, so none can enter a proof.
--
-- The axiom census reads each constant's term as the environment RECORDS it,
-- and a record is not a kernel verdict: a meta-program can write a constant
-- into the environment without the kernel (the private `Environment.add`,
-- reached through `evalConst`). Measured 2026-09-29 on a scratch copy: a module
-- doing exactly that planted `theorem review_forged_false : False := Nat.zero`
-- plus a theorem using it, and the census and build passed (`#print axioms`
-- says "does not depend on any axioms"). So the census ends with a KERNEL
-- REPLAY: `Lean.Environment.replay` (Lean core, `Lean/Replay.lean`, the engine
-- of lean4checker) re-sends every safe `TrustIr.*` constant to the kernel,
-- starting from the library's external imports (`Init` today), so each one is
-- re-admitted from its stored term, and an inductive's constructors and
-- recursors must equal the ones the kernel regenerates. The plant above is
-- refused by name: "(kernel) declaration type mismatch,
-- 'TrustIr.review_forged_false' has type Nat but it is expected to have type
-- False" (so is the same plant inside a fixture module).
--
-- `native_decide`. The kernel decides `Lean.reduceBool aux` by running the
-- compiled code of the `_nativeDecide_N` auxiliary, which a replayed
-- environment does not carry: replayed verbatim, the first fixture theorem
-- fails "(kernel) unknown declaration '..._nativeDecide_1'" (measured). So in
-- `nativeDecideModules` (the only modules where the census admits
-- `Lean.ofReduceBool`) every site `Lean.ofReduceBool aux b h` has its
-- evidence `h` replaced by a premise `Lean.reduceBool aux = b`, and that
-- premise enters the replayed environment only after `evalBool` runs `aux`'s
-- compiled code in THIS process and gets `b`. The kernel therefore re-checks
-- all of such a proof but the evaluation, and the evaluation is re-run; a
-- forged site asserting the wrong value is refused ("native-evaluation: ...
-- evaluates to true; the proof asserts false", measured). The re-run uses the
-- same compiled code the build's kernel ran, so the fixtures stay what the
-- census calls them: evaluations, trusting the Lean compiler and runtime.
-- Anywhere else a `Lean.ofReduceBool` is left as it is, and the replay
-- refuses it beside the census.
--
-- Lean 4.30's native_decide instead stores a fresh axiom of the form
-- `closedBoolExpression = true`. Only in the same two fixture modules, its
-- actual origin, zero universe parameters, generated-site spelling and complete
-- closed Boolean-equality type are checked; the stored Boolean expression is
-- compiled and evaluated again with the standard safe/type checks. A successful
-- runtime assertion is replayed as a theorem conditional on a fresh premise of
-- exactly that stored equality. No premise is inserted for a false/failed site.
-- Other modules cannot inherit this permission. Raw declared axioms remain
-- reported, and `fixture-evaluation-axioms` separately accounts for these tests;
-- they are not additional permanent logical axioms. They remain compiler/runtime
-- evaluations, just as the canonical native_decide fixtures do.
--
-- Not replayed: a `partial` definition's `_unsafe_rec` body (safety
-- `partial`), which the replay engine skips. The kernel refuses a safe
-- declaration that names one ("safe declaration must not contain partial
-- declaration"), and a replayed constant naming one fails as unknown
-- (measured with a forged `partial` definition of `False` and a theorem using
-- it), so none can enter a replayed proof. The census line prints `replayed`
-- and `replay-skipped-partial`, and the gate checks they add up to
-- `safe-constants`.
--
-- The replay re-runs the SAME kernel that admitted each constant during the
-- build. It closes admission WITHOUT the kernel (the plant above, or
-- `debug.skipKernelTC` on a toolchain that has it); it is not a second kernel
-- and says nothing about a kernel bug (TRUST.md item 1). Lean 4.8.0 ships no
-- `leanchecker` executable; this is the core function that executable wraps.
--
-- What this census cannot see: an `example` never enters the environment, so
-- the gate catches a placeholder in one from the build log instead ("declaration
-- uses 'sorry'", which Lake replays on a cached build).
--
-- "Depends on" is the SAME relation `#print axioms` uses
-- (`Lean.Elab.Command.CollectAxioms.collect` in Lean 4.8.0): a constant's type
-- and value, a constructor's or recursor's type, an inductive's type and its
-- constructors. `axiomsOf` memoizes it over the whole library instead of
-- re-walking the Lean core closure per constant (2 min to ~seconds, measured
-- 2026-09-29).
--
-- Run: `lake env lean ProofCensus.lean` in this directory, after
-- `lake build TrustIr`. Deliberately NOT a module of any `lean_lib`: the
-- census is a check ON the library, never part of it. On refusal it exits 1
-- with an `error:`; the green path prints one `lean-proofs census:` line,
-- which the gate parses (it also checks the replay ledger, see above).

import Lean
import Lean.Replay
import TrustIr

namespace TrustIrProofCensus

open Lean

/-- Keep the same lookup default and deterministic sample under both APIs. -/
macro "censusNameMapFindD " table:term:max key:term:max fallback:term:max : term => do
  if Lean.versionString == "4.8.0" then `(($table).findD $key $fallback)
  else if Lean.versionString == "4.30.0-rc2" then `(($table).getD $key $fallback)
  else Lean.Macro.throwError "unsupported Lean compiler for census name maps"

macro "censusEnumerate " values:term:max : term => do
  if Lean.versionString == "4.8.0" then `(($values).enum)
  else if Lean.versionString == "4.30.0-rc2" then
    `((List.range ($values).length).zip $values)
  else Lean.Macro.throwError "unsupported Lean compiler for census enumeration"

/-- Read stored private declarations on modern Lean and enumerate both actual
    constant-map stages before applying the unchanged module-origin filter. -/
macro "censusStoredEnvironment " environment:term:max : term => do
  if Lean.versionString == "4.8.0" then pure environment
  else if Lean.versionString == "4.30.0-rc2" then `(($environment).setExporting false)
  else Lean.Macro.throwError "unsupported Lean compiler for stored census environment"

macro "censusConstants " environment:term:max : term => do
  if Lean.versionString == "4.8.0" then `(($environment).constants.map₁.toList)
  else if Lean.versionString == "4.30.0-rc2" then `(($environment).constants.toList)
  else Lean.Macro.throwError "unsupported Lean compiler for complete constant census"

/-- Modern replay returns a kernel-backed environment whose new declarations
    need not appear in the elaborator's asynchronous lookup. Check the actual
    returned kernel map; retain canonical lookup on Lean 4.8. -/
macro "censusReplayContains " environment:term:max name:term:max : term => do
  if Lean.versionString == "4.8.0" then `(($environment).contains $name)
  else if Lean.versionString == "4.30.0-rc2" then
    `((($environment).toKernelEnv.find? $name).isSome)
  else Lean.Macro.throwError "unsupported Lean compiler for replay presence check"

/-- Look up records in the same actual kernel population being enumerated. -/
macro "censusStoredFind? " environment:term:max name:term:max : term => do
  if Lean.versionString == "4.8.0" then `(($environment).find? $name)
  else if Lean.versionString == "4.30.0-rc2" then
    `(($environment).toKernelEnv.find? $name)
  else Lean.Macro.throwError "unsupported Lean compiler for stored constant lookup"

/-- The axioms a safe `TrustIr.*` constant may depend on: the Lean-core trio
and the one first-party trust boundary (TRUST.md item 2). -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound, ``TrustIr.ay_sound_unsat]

/-- Permanent logical axioms. Modern fixture assertion declarations are separate
    compiled evaluations, validated and replaced by exact runtime premises. -/
def declarableAxioms : List Name := [``TrustIr.ay_sound_unsat]

/-- The modules whose constants may ALSO rest on `Lean.ofReduceBool`: the
executable fixtures, whose theorems are `native_decide` EVALUATIONS of the
executable semantics. They trust the Lean compiler and runtime, not only the
kernel, so they are tests and not proofs; everywhere else the axiom is
refused. `scripts/check_enforcement_links.py` reads this list (the backticked
names between the brackets) so a theorem of these modules never witnesses the
`(lean-theorem)` class. -/
def nativeDecideModules : List Name :=
  [`TrustIr.Semantics.ExecutableFixtures, `TrustIr.Semantics.FloatFixtures]

/-- The modules the census audits: the `TrustIr` library, root included.
`TrustIrEval` (the execution oracle of gate 12) is not imported here. -/
def isAuditedModule (m : Name) : Bool := m.getRoot == `TrustIr

/-- The constants `ci`'s own kernel term names, by the `#print axioms`
relation (see the header). -/
def dependencies (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

structure Memo where
  /-- Completed, exact axiom sets. -/
  done : trustIrHashMap Name (Array Name) := {}
  /-- Constants being expanded, with their DFS depth. -/
  onStack : trustIrHashMap Name Nat := {}

/-- The axioms `c` depends on, memoized. Returns the set and the shallowest
in-progress ancestor it touched (a cycle: an inductive and its constructors).
A result is memoized only when it touched nothing shallower than `c` itself,
so a partial set inside a cycle is never reused. `#print axioms` does not
descend into an axiom's type; neither does this (an axiom is a leaf). -/
partial def axiomsOf (env : Environment) (c : Name) (depth : Nat) :
    StateM Memo (Array Name × Option Nat) := do
  let s ← get
  if let some r := trustIrHashMapFind? s.done c then return (r, none)
  if let some d := trustIrHashMapFind? s.onStack c then return (#[], some d)
  modify fun s => { s with onStack := s.onStack.insert c depth }
  let mut acc : Array Name := #[]
  let mut low : Option Nat := none
  match censusStoredFind? env c with
  | some (.axiomInfo _) => acc := #[c]
  | some ci =>
    for d in dependencies ci do
      let (r, l) ← axiomsOf env d (depth + 1)
      for a in r do
        unless acc.contains a do acc := acc.push a
      low := match low, l with
        | none, x => x
        | x, none => x
        | some a, some b => some (min a b)
  | none => pure ()
  modify fun s => { s with onStack := s.onStack.erase c }
  if low.all (· ≥ depth) then
    modify fun s => { s with done := s.done.insert c acc }
    return (acc, none)
  return (acc, low)

def sortNames (xs : Array Name) : Array Name :=
  xs.qsort (fun a b => a.toString < b.toString)

namespace DirectStoredAxioms

/-- Independent visited-set traversal of actual stored types and terms.
    This retains the canonical collector's axiom-leaf relation and all eight
    ConstantInfo cases. It does not use the census memo or imported axiom caches. -/
structure State where
  visited : NameSet := {}
  axioms : Array Name := #[]

abbrev M := ReaderT Environment (StateM State)

partial def collect (name : Name) : M Unit := do
  let collectExpr (expression : Expr) : M Unit := expression.getUsedConstants.forM collect
  let state ← get
  unless state.visited.contains name do
    modify fun state => {state with visited := state.visited.insert name}
    let env ← read
    match censusStoredFind? env name with
    | some (.axiomInfo _) => modify fun state => {state with axioms := state.axioms.push name}
    | some (.defnInfo value) => collectExpr value.type *> collectExpr value.value
    | some (.thmInfo value) => collectExpr value.type *> collectExpr value.value
    | some (.opaqueInfo value) => collectExpr value.type *> collectExpr value.value
    | some (.quotInfo _) => pure ()
    | some (.ctorInfo value) => collectExpr value.type
    | some (.recInfo value) => collectExpr value.type
    | some (.inductInfo value) => collectExpr value.type *> value.ctors.forM collect
    | none => pure ()

end DirectStoredAxioms

/-- Canonical Lean keeps its original independent collector. Modern Lean's
    public collector uses imported caches, so use the explicit stored-term walk
    above to preserve the independent crosscheck instead of trusting that cache. -/
macro "censusUnmemoizedCollect" : term => do
  if Lean.versionString == "4.8.0" then `(Lean.Elab.Command.CollectAxioms.collect)
  else if Lean.versionString == "4.30.0-rc2" then `(TrustIrProofCensus.DirectStoredAxioms.collect)
  else Lean.Macro.throwError "unsupported Lean compiler for direct axiom census"

/-- The unmemoized canonical axiom relation, run from `roots` with ONE shared
    visited set: the exact union of their axiom sets. -/
def exactAxioms (env : Environment) (roots : Array Name) : Array Name :=
  let go := roots.forM censusUnmemoizedCollect
  let (_, state) := (go.run env).run {}
  state.axioms

/-- Set equality of two small axiom lists. -/
def sameSet (a b : Array Name) : Bool :=
  a.all b.contains && b.all a.contains

/-- Every `crossCheckStride`-th theorem (by name) is re-collected with the
unmemoized traversal and compared with `axiomsOf`: the memo's per-constant
answers are sampled against `#print axioms` on every run, beside the exact
comparison of the union. -/
def crossCheckStride : Nat := 16

/-- The imports the audited modules take from OUTSIDE the library (`Init`
alone at the time of writing). The replay starts from exactly these, so every
`TrustIr.*` constant is re-admitted, none inherited. -/
def externalImports (env : Environment) : Array Import := Id.run do
  let modules := env.header.moduleNames
  let mut base : Array Import := #[]
  for i in [:modules.size] do
    if isAuditedModule modules[i]! then
      for imp in env.header.moduleData[i]!.imports do
        unless isAuditedModule imp.module || base.any (·.module == imp.module) do
          base := base.push imp
  return base

/-- The name of the replay premise that stands for ONE compiler evaluation,
`Lean.reduceBool aux = b`. The premise exists only in the replayed
environment, and only after `aux` was evaluated to `b` (see `evalBool`). -/
def evaluationPremise (aux : Name) (b : Bool) : Name :=
  (`TrustIrProofCensus.evaluated ++ Name.mkSimple (toString b)) ++ aux

/-- The `(aux, b)` a premise name stands for. -/
def premiseSite? (p : Name) : Option (Name × Bool) :=
  [true, false].findSome? fun b =>
    let pre := `TrustIrProofCensus.evaluated ++ Name.mkSimple (toString b)
    if pre.isPrefixOf p && p != pre then some (p.replacePrefix pre .anonymous, b) else none

/-- The one shape `native_decide` leaves in a term: `Lean.ofReduceBool aux b h`
with `aux` a closed constant and `b` a `Bool` literal. -/
def evaluationSite? (e : Expr) : Option (Name × Bool) :=
  if e.isAppOfArity ``Lean.ofReduceBool 3 then
    match e.appFn!.appFn!.appArg!, e.appFn!.appArg! with
    | .const aux [], .const ``Bool.true [] => some (aux, true)
    | .const aux [], .const ``Bool.false [] => some (aux, false)
    | _, _ => none
  else none

/-- `ci` with the evidence `h` of every `native_decide` site replaced by the
premise for its evaluation. Everything else in the term is untouched, so the
kernel re-checks all of it; a use of `Lean.ofReduceBool` of any other shape is
left as it is, and the replay then refuses it (the kernel cannot run the
compiler). -/
def withEvaluationPremises (ci : ConstantInfo) : ConstantInfo :=
  let rw (v : Expr) : Expr := v.replace fun e =>
    (evaluationSite? e).map fun (aux, b) =>
      mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst aux) (toExpr b)
        (mkConst (evaluationPremise aux b))
  match ci with
  | .thmInfo v => .thmInfo { v with value := rw v.value }
  | .defnInfo v => .defnInfo { v with value := rw v.value }
  | .opaqueInfo v => .opaqueInfo { v with value := rw v.value }
  | ci => ci

/-- The premise `Lean.reduceBool aux = b` as an axiom of the replayed
environment. -/
def premiseAxiom (aux : Name) (b : Bool) : ConstantInfo :=
  .axiomInfo {
    name := evaluationPremise aux b, levelParams := [], isUnsafe := false
    type := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool)
      (mkApp (mkConst ``Lean.reduceBool) (mkConst aux)) (toExpr b) }

unsafe def evalBoolUnsafe (env : Environment) (n : Name) : Except String Bool :=
  env.evalConst Bool {} n

/-- Run the compiled code of the closed `Bool` constant `n`, as the kernel's
`Lean.reduceBool` does: the Lean compiler and runtime, the trust
`Lean.ofReduceBool` names. -/
@[implemented_by evalBoolUnsafe]
opaque evalBool (env : Environment) (n : Name) : Except String Bool

/-- Modern native_decide records a closed Boolean equality as a fresh axiom.
    Its spelling identifies a candidate only: actual module, complete type,
    closedness, compiled result and replay are all checked independently. -/
structure FixtureEvaluation where
  original : AxiomVal
  expression : Expr

def fixtureEvaluationSite? (moduleName : Name) (ci : ConstantInfo) : Option FixtureEvaluation := do
  if Lean.versionString != "4.30.0-rc2" || !nativeDecideModules.contains moduleName then none
  else do
    let .axiomInfo original := ci | none
    unless !original.isUnsafe && original.levelParams.isEmpty do none
    let generated := match original.name with
      | .str (.str (.str _ "_native") "native_decide") suffix => suffix.startsWith "ax_"
      | _ => false
    unless generated && original.type.isAppOfArity ``Eq 3 do none
    let args := original.type.getAppArgs
    unless args[0]!.isConstOf ``Bool && args[2]!.isConstOf ``Bool.true do none
    let expression := args[1]!
    unless !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars do none
    some {original, expression}

def fixtureEvaluationPremise (site : FixtureEvaluation) : Name :=
  `TrustIrProofCensus.evaluatedFixture ++ site.original.name

/-- An evaluated value must not hide a forbidden axiom in an erased proof.
    Inspect actual stored dependencies separately from the axiom-leaf census;
    neither a generated name nor a true compiled result grants that permission. -/
def fixtureEvaluationForbiddenDependencies (env : Environment) (site : FixtureEvaluation) : Array Name :=
  (exactAxioms env (site.original.type.getUsedConstants ++ site.expression.getUsedConstants)).filter
    (fun name => !allowedAxioms.contains name)

def fixtureEvaluationPremiseAxiom (site : FixtureEvaluation) : ConstantInfo :=
  .axiomInfo {site.original with name := fixtureEvaluationPremise site}

/-- Replace a runtime assertion by a theorem conditional on precisely its
    evaluated Boolean equality; the premise is inserted only after evaluation. -/
def fixtureEvaluationReplay (site : FixtureEvaluation) : ConstantInfo :=
  .thmInfo {
    name := site.original.name
    levelParams := []
    type := site.original.type
    value := mkConst (fixtureEvaluationPremise site) }

unsafe def evalFixtureBoolUnsafe (expression : Expr) : MetaM Bool :=
  Meta.evalExpr Bool (mkConst ``Bool) expression

/-- Actual safe compilation and evaluation of the stored closed Bool expression.
    The underlying evaluator keeps its default safety and type checks. -/
@[implemented_by evalFixtureBoolUnsafe]
opaque evalFixtureBool (expression : Expr) : MetaM Bool

/-- Exercise refusal and actual false/true evaluation without inserting any
    synthetic assertion into the environment or minting a replay premise. -/
def checkFixtureEvaluationControls : Elab.Command.CommandElabM Unit := do
  if Lean.versionString == "4.30.0-rc2" then
    let equality (value : Expr) :=
      mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) value (mkConst ``Bool.true)
    let original : AxiomVal := {
      name := `TrustIrProofCensus.control._native.native_decide.ax_control
      levelParams := [], type := equality (mkConst ``Bool.true), isUnsafe := false }
    let admittedModule := `TrustIr.Semantics.ExecutableFixtures
    unless (fixtureEvaluationSite? admittedModule (.axiomInfo original)).isSome do
      throwError "fixture-evaluation-control: valid closed equality refused"
    unless (fixtureEvaluationSite? `TrustIr.Proofs.Control (.axiomInfo original)).isNone do
      throwError "fixture-evaluation-control: nonfixture module accepted"
    for malformed in #[{original with type := mkConst ``True},
        {original with levelParams := [`u]}, {original with isUnsafe := true},
        {original with type := equality (.fvar ⟨`openControl⟩)}] do
      unless (fixtureEvaluationSite? admittedModule (.axiomInfo malformed)).isNone do
        throwError "fixture-evaluation-control: malformed or open assertion accepted"
    let actualFalse ← Elab.Command.liftTermElabM <| evalFixtureBool (mkConst ``Bool.false)
    let actualTrue ← Elab.Command.liftTermElabM <| evalFixtureBool (mkConst ``Bool.true)
    unless !actualFalse && actualTrue do
      throwError "fixture-evaluation-control: compiled false/true results disagree"
    let foreign := `TrustIrProofCensus.foreignControlEquality
    let erasedDependencies ← Elab.Command.liftTermElabM <| withoutModifyingEnv do
      let type ← Meta.mkEq (mkConst ``Bool) (mkConst ``Bool)
      addDecl (.axiomDecl {name := foreign, levelParams := [], type, isUnsafe := false})
      let expression := mkApp4 (mkConst ``Eq.mp [levelOne])
        (mkConst ``Bool) (mkConst ``Bool) (mkConst foreign) (mkConst ``Bool.true)
      let site : FixtureEvaluation := {
        original := {original with type := equality expression}, expression }
      return fixtureEvaluationForbiddenDependencies (← getEnv) site
    unless erasedDependencies.contains foreign do
      throwError "fixture-evaluation-control: erased foreign axiom was not rejected"

/-- Re-send `targets` to the kernel on top of the library's external imports
(`Lean.Environment.replay`; it throws the kernel's refusal). Returns the
targets the replayed environment does not hold afterwards, which must be none:
a constant the engine silently passed over would otherwise count as replayed. -/
def kernelReplay (env : Environment) (targets : trustIrHashMap Name ConstantInfo) :
    IO (Array Name) := do
  let baseEnv ← importModules (externalImports env) {} 0
  let replayed ← Environment.replay targets baseEnv
  return targets.fold (init := #[]) fun acc n _ =>
    if censusReplayContains replayed n then acc else acc.push n

end TrustIrProofCensus

open Lean Elab Command TrustIrProofCensus in
run_cmd do
  checkFixtureEvaluationControls
  let importedEnv ← getEnv
  let env := censusStoredEnvironment importedEnv
  let modules := env.header.moduleNames
  let mut audited : Array (Name × Name × ConstantInfo) := #[]
  let mut auditedModules : NameSet := {}
  for (name, ci) in censusConstants env do
    if ci.isUnsafe then continue
    if let some idx := env.getModuleIdxFor? name then
      let m := modules[idx.toNat]!
      if isAuditedModule m then
        audited := audited.push (name, m, ci)
        auditedModules := auditedModules.insert m
  if audited.isEmpty then
    throwError "lean-proofs census: no safe constant of a `TrustIr.*` module is in \
      the environment; an empty census is not a pass"
  let mut problems : Array String := #[]
  let mut fixtureEvaluations : trustIrHashMap Name FixtureEvaluation := {}
  -- These are compiled tests, never additional formal axioms. Failed or
  -- malformed sites retain their ordinary forbidden/undeclared refusals.
  for (name, moduleName, ci) in audited do
    if let some site := fixtureEvaluationSite? moduleName ci then
      let forbidden := fixtureEvaluationForbiddenDependencies env site
      if !forbidden.isEmpty then
        problems := problems.push s!"native-evaluation: {name} has forbidden stored dependencies {sortNames forbidden}"
      else
        try
          let actual ← liftTermElabM <| evalFixtureBool site.expression
          if actual then
            fixtureEvaluations := fixtureEvaluations.insert name site
          else
            problems := problems.push s!"native-evaluation: {name} evaluates to false; the fixture asserts true"
        catch error =>
          problems := problems.push s!"native-evaluation: {name}: {← error.toMessageData.toString}"
  let mut memo : Memo := {}
  let mut theorems := 0
  let mut declared : Array Name := #[]
  let mut violations : Array (Name × Name × Bool) := #[]
  let mut theoremsByAxiom : NameMap Nat := {}
  for (name, m, ci) in audited do
    let isThm := match ci with | .thmInfo _ => true | _ => false
    if isThm then theorems := theorems + 1
    if let .axiomInfo _ := ci then declared := declared.push name
    let ((axs, _), memo') := (axiomsOf env name 0).run memo
    memo := memo'
    let direct := dependencies ci
    for ax in axs do
      if isThm then
        theoremsByAxiom := theoremsByAxiom.insert ax ((censusNameMapFindD theoremsByAxiom ax 0) + 1)
      let admitted := allowedAxioms.contains ax ||
        (nativeDecideModules.contains m &&
          (ax == ``Lean.ofReduceBool || (trustIrHashMapFind? fixtureEvaluations ax).isSome))
      -- A declared axiom depends on itself; that is the declaration rule's
      -- business below, not a use.
      unless admitted || ax == name do
        violations := violations.push (ax, name, direct.contains ax)
  -- Self-check of the memo against the `#print axioms` traversal: the union
  -- exactly, and a deterministic sample of theorems one by one.
  let mut memoUnion : Array Name := #[]
  for (name, _, _) in audited do
    if let some r := trustIrHashMapFind? memo.done name then
      for a in r do
        unless memoUnion.contains a do memoUnion := memoUnion.push a
    else
      problems := problems.push s!"census-self-check: no memoized result for {name}"
  let exactUnion := exactAxioms env (audited.map (·.1))
  unless sameSet memoUnion exactUnion do
    problems := problems.push s!"census-self-check: memoized union {sortNames memoUnion} \
      differs from the `#print axioms` union {sortNames exactUnion}"
  let sampled := (censusEnumerate ((sortNames (audited.filterMap fun (n, _, ci) =>
    match ci with | .thmInfo _ => some n | _ => none)).toList)).filterMap
      fun (i, n) => if i % crossCheckStride == 0 then some n else none
  for n in sampled do
    let exact := exactAxioms env #[n]
    let memoed := (trustIrHashMapFind? memo.done n).getD #[]
    unless sameSet exact memoed do
      problems := problems.push s!"census-self-check: {n}: memoized {sortNames memoed} \
        but `#print axioms` says {sortNames exact}"
  for ax in sortNames declared do
    unless declarableAxioms.contains ax || (trustIrHashMapFind? fixtureEvaluations ax).isSome do
      problems := problems.push s!"undeclared-axiom {ax}: a safe `axiom` in a TrustIr \
        module beyond {declarableAxioms}"
  for ax in declarableAxioms do
    unless declared.contains ax do
      problems := problems.push s!"missing-axiom {ax}: the documented boundary is no \
        longer declared; move TRUST.md item 2 and this census together"
  -- The kernel replay (see the header): every audited constant except the
  -- two classes the header names, counted so the ledger adds up.
  let mut replayTargets : trustIrHashMap Name ConstantInfo := {}
  let mut skippedPartial := 0
  let mut premises : NameSet := {}
  for (name, m, ci) in audited do
    if ci.isPartial then
      skippedPartial := skippedPartial + 1
      continue
    -- Only where the census admits `Lean.ofReduceBool`; anywhere else the
    -- replay refuses it, beside the census.
    let ci := match trustIrHashMapFind? fixtureEvaluations name with
      | some site => fixtureEvaluationReplay site
      | none => if nativeDecideModules.contains m then withEvaluationPremises ci else ci
    for c in ci.getUsedConstantsAsSet do
      if (premiseSite? c).isSome then premises := premises.insert c
    replayTargets := replayTargets.insert name ci
  let replayed := replayTargets.size
  -- Every such premise has already been evaluated positively above. Its type
  -- is the actual stored equality, with no proposition inferred from a name.
  for (_, site) in fixtureEvaluations.toList do
    let premise := fixtureEvaluationPremise site
    if censusReplayContains env premise || replayTargets.contains premise then
      problems := problems.push s!"native-evaluation: runtime premise collides with stored declaration {premise}"
    else
      replayTargets := replayTargets.insert premise (fixtureEvaluationPremiseAxiom site)
  -- Each premise is admitted only after the compiled code agrees.
  for p in premises do
    let some (aux, b) := premiseSite? p | continue
    match evalBool env aux with
    | .ok v =>
      if v == b then
        if censusReplayContains env p || replayTargets.contains p then
          problems := problems.push s!"native-evaluation: runtime premise collides with stored declaration {p}"
        else
          replayTargets := replayTargets.insert p (premiseAxiom aux b)
      else
        problems := problems.push s!"native-evaluation: {aux} evaluates to {v}; the \
          proof asserts {b}"
    | .error e => problems := problems.push s!"native-evaluation: {aux}: {e}"
  match ← (kernelReplay env replayTargets).toBaseIO with
  | .ok missing =>
    for n in sortNames missing do
      problems := problems.push s!"kernel-replay: {n} is not in the replayed environment"
  | .error e =>
    -- The kernel's message spans lines ("has type\n  Nat\nbut ..."); one
    -- refusal per line keeps the gate's output parseable.
    let flat := String.intercalate " " (((toString e).splitOn "\n").map String.trim)
    problems := problems.push s!"kernel-replay: {flat}"
  let sorted := violations.qsort fun (a1, n1, _) (a2, n2, _) =>
    a1.toString < a2.toString || (a1 == a2 && n1.toString < n2.toString)
  for (ax, name, direct) in sorted do
    let how := if direct then "direct" else "inherited"
    problems := problems.push s!"forbidden-axiom {ax} in {name} ({how})"
  let byAxiom := String.intercalate ", "
    ((sortNames (theoremsByAxiom.toList.map (·.1)).toArray).toList.map fun ax =>
      s!"{ax}={censusNameMapFindD theoremsByAxiom ax 0}")
  let importedModules := (modules.filter isAuditedModule).size
  let logicalDeclared := declared.filter declarableAxioms.contains
  let summary := s!"lean-proofs census: modules={auditedModules.size} \
    safe-constants={audited.size} theorems={theorems} \
    theorems-by-axiom=[{byAxiom}] declared-axioms={sortNames declared} \
    imported-modules={importedModules} cross-checked={sampled.length} \
    replayed={replayed} replay-evaluations={premises.size + fixtureEvaluations.size} \
    fixture-evaluation-axioms={fixtureEvaluations.size} \
    logical-declared-axioms={sortNames logicalDeclared} \
    replay-skipped-partial={skippedPartial}"
  if problems.isEmpty then
    logInfo summary
  else
    throwError (String.intercalate "\n" (summary :: "lean-proofs census REFUSED:" ::
      problems.toList.map ("  " ++ ·)))
