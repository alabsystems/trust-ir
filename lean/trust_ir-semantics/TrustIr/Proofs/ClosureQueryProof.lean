-- Copyright 2026 Andrew Yates | Apache-2.0
import Lean
import TrustIr.DecodedClosureStorage

namespace TrustIr.ClosureQueryProof

/-- Recover the actual returned state; this never chooses or normalizes it. -/
theorem map_fst_ok_exists {ε α β : Type} (q : Except ε (α × β))
    (value : α) (h : q.map Prod.fst = .ok value) :
    ∃ after, q = .ok (value, after) := by
  cases q with
  | error error => cases h
  | ok pair =>
    rcases pair with ⟨actual, after⟩
    have same : actual = value := Except.ok.inj h
    cases same
    exact ⟨after, rfl⟩

theorem map_fst_error {ε α β : Type} (q : Except ε (α × β))
    (error : ε) (h : q.map Prod.fst = .error error) : q = .error error := by
  cases q with
  | error actual =>
    have same : actual = error := Except.error.inj h
    cases same
    rfl
  | ok pair => cases h

theorem error_ne_ok {ε α : Type} (error : ε) (value : α) :
    (Except.error error : Except ε α) ≠ Except.ok value := by
  intro h
  cases h

theorem ok_ne_error {ε α : Type} (value : α) (error : ε) :
    (Except.ok value : Except ε α) ≠ Except.error error := by
  intro h
  cases h

/-- Structural inequality gives a false comparator, using its proved soundness. -/
theorem list_ne_false (left right : List Ty) (different : left ≠ right) :
    closureTyListEq left right = false := by
  cases checked : closureTyListEq left right with
  | false => rfl
  | true => exact False.elim (different (closureTyListEq_sound left right checked))

end TrustIr.ClosureQueryProof

elab "trustIrRegisterClosureQueryEquations" : command => do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

-- Caller explicitly names the ONLY permitted open ABI variables. No implicit context capture.
elab "trustIrSplitClosureQuery" hypothesisName:ident "allowing" "[" allowed:ident,* "]" : tactic => Lean.Elab.Tactic.withMainContext do
  let mut permitted : Array Lean.FVarId := #[]
  for name in allowed.getElems do
    let some entry := (← Lean.getLCtx).findFromUserName? name.getId
      | Lean.throwError "closure query missing allowed ABI variable"
    match entry with
    | .cdecl _ _ _ _ _ _ => pure ()
    | .ldecl _ _ _ _ _ _ _ =>
      Lean.throwError "closure query ABI must be an explicit parameter"
    let type ← Lean.instantiateMVars entry.type
    unless type.isConstOf ``TrustIr.SignatureAbi do
      Lean.throwError "closure query allowlist permits only SignatureAbi parameters"
    unless !permitted.contains entry.fvarId do Lean.throwError "duplicate allowed ABI parameter"
    permitted := permitted.push entry.fvarId
  let some declaration := (← Lean.getLCtx).findFromUserName? hypothesisName.getId
    | Lean.throwError "closure query missing query equality"
  let equalityType ← Lean.instantiateMVars declaration.type
  unless equalityType.isAppOfArity ``Eq 3 do
    Lean.throwError "closure query equality required"
  let arguments := equalityType.getAppArgs
  let originalLhs := arguments[1]!
  let originalRhs := arguments[2]!
  let candidates ← IO.mkRef (#[] : Array Lean.Expr)
  let visited ← IO.mkRef (0 : Nat)
  (← Lean.Elab.Tactic.getMainTarget).forEach fun expression => do
    let count ← visited.modifyGet fun n => (n + 1, n + 1)
    unless count ≤ 200000 do Lean.throwError "closure query selection bound"
    let application := expression.consumeMData
    if let .const name _ := application.getAppFn then
      if let some information ← Lean.Meta.getMatcherInfo? name then
        if application.getAppNumArgs == information.arity &&
            information.numDiscrs == 1 && information.numAlts == 2 &&
            information.discrInfos[0]!.hName?.isSome then
          let query := (application.getAppArgs)[information.getFirstDiscrPos]!
          if query.consumeMData.isAppOfArity `TrustIr.SourceLayout.Session.query 3 then
            unless !query.hasLooseBVars && !query.hasMVar && !originalLhs.hasMVar do
              Lean.throwError "closure query unresolved or loose variables"
            for subject in #[query, originalLhs] do
              subject.forEach fun node => do
                if let .fvar id := node then
                  unless permitted.contains id do
                    Lean.throwError "closure query variable outside explicit ABI allowlist"
            let same ← Lean.withoutModifyingState do
              Lean.Meta.isDefEq originalLhs query
            if same then
              let prior ← candidates.get
              unless prior.isEmpty do Lean.throwError "closure query ambiguous query matcher"
              candidates.set #[application]
  let selected ← candidates.get
  unless selected.size == 1 do Lean.throwError "closure query unique query matcher required"
  let application := selected[0]!
  let .const matcherName _ := application.getAppFn
    | Lean.throwError "closure query selected matcher head required"
  let some information ← Lean.Meta.getMatcherInfo? matcherName
    | Lean.throwError "closure query selected matcher metadata required"
  let discriminator := (application.getAppArgs)[information.getFirstDiscrPos]!
  let exactType ← Lean.Meta.mkEq discriminator originalRhs
  let goal ← Lean.Elab.Tactic.getMainGoal
  let changed ← goal.changeLocalDecl declaration.fvarId exactType (checkDefEq := true)
  let branches ← Lean.Meta.Split.splitMatch changed application
  Lean.Elab.Tactic.replaceMainGoal branches

-- No context variable is admitted implicitly.
private def trustIrClosureCheckWithinAbi (permitted : Array Lean.FVarId)
    (expression : Lean.Expr) : Lean.Elab.Tactic.TacticM Bool := do
  if expression.hasMVar || expression.hasLooseBVars then return false
  if !expression.hasFVar then return true
  let accepted ← IO.mkRef true
  expression.forEach fun node => do
    if let .fvar id := node then
      unless permitted.contains id do accepted.set false
  accepted.get

-- Retype only a complete checked result equality, never its Boolean argument.
elab "trustIrRetypeClosureCheck" hypothesisName:ident "allowing" "[" allowed:ident,* "]" : tactic => Lean.Elab.Tactic.withMainContext do
  let mut permitted : Array Lean.FVarId := #[]
  for name in allowed.getElems do
    let some entry := (← Lean.getLCtx).findFromUserName? name.getId
      | Lean.throwError "closure query missing allowed ABI variable"
    match entry with
    | .cdecl _ _ _ _ _ _ => pure ()
    | .ldecl _ _ _ _ _ _ _ =>
      Lean.throwError "closure query ABI must be an explicit parameter"
    let type ← Lean.instantiateMVars entry.type
    unless type.isConstOf ``TrustIr.SignatureAbi do
      Lean.throwError "closure query allowlist permits only SignatureAbi parameters"
    unless !permitted.contains entry.fvarId do Lean.throwError "duplicate allowed ABI parameter"
    permitted := permitted.push entry.fvarId
  let some declaration := (← Lean.getLCtx).findFromUserName? hypothesisName.getId
    | Lean.throwError "Q13 missing checked-result equality"
  let equalityType ← Lean.instantiateMVars declaration.type
  unless equalityType.isAppOfArity ``Eq 3 do
    Lean.throwError "Q13 checked-result equality required"
  let arguments := equalityType.getAppArgs
  let originalLhs := arguments[1]!
  let originalRhs := arguments[2]!
  unless ← trustIrClosureCheckWithinAbi permitted originalLhs do
    Lean.throwError "closure check outside explicit ABI scope"
  let candidates ← IO.mkRef (#[] : Array Lean.Expr)
  let visited ← IO.mkRef (0 : Nat)
  (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).forEach fun expression => do
    let count ← visited.modifyGet fun n => (n + 1, n + 1)
    unless count ≤ 200000 do Lean.throwError "Q13 selection bound"
    let application := expression.consumeMData
    if ← trustIrClosureCheckWithinAbi permitted application then
      if let .const name _ := application.getAppFn then
        let mut eligible := (name == ``Bool.casesOn || name == ``Bool.rec) &&
          application.getAppNumArgs == 4
        if let some information ← Lean.Meta.getMatcherInfo? name then
          if application.getAppNumArgs == information.arity && information.numDiscrs == 1 then
            let discriminator := (application.getAppArgs)[information.getFirstDiscrPos]!
            let isBoolean ← Lean.withoutModifyingState do
              Lean.Meta.withTransparency .default do
                Lean.Meta.isDefEq (← Lean.Meta.inferType discriminator) (Lean.mkConst ``Bool)
            eligible := eligible || isBoolean
        if eligible then
          let same ← Lean.withoutModifyingState do
            Lean.Meta.withTransparency .default (Lean.Meta.isDefEq application originalLhs)
          if same then
            unless (← candidates.get).isEmpty do Lean.throwError "Q13 ambiguous checked result"
            candidates.set #[application]
  let selected ← candidates.get
  unless selected.size == 1 do Lean.throwError "Q13 unique whole checked result required"
  let exactType ← Lean.Meta.mkEq selected[0]! originalRhs
  let goal ← Lean.Elab.Tactic.getMainGoal
  let changed ← goal.changeLocalDecl declaration.fvarId exactType (checkDefEq := true)
  Lean.Elab.Tactic.replaceMainGoal [changed]
