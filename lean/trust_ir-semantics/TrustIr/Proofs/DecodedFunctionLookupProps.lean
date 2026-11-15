-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.DecodedFunctionLookup

namespace TrustIrEval.FunctionLookup
open TrustIr

/-- First insertion preserves every occupied payload, including an error. -/
theorem insertFirst_find {α : Type} (index : NatIndex α) (key query : Nat) (value : α) :
    (insertFirst index key value).find? query =
      match index.find? query with
      | some previous => some previous
      | none => if query = key then some value else none := by
  by_cases same : query = key
  · subst query
    cases found : index.find? key <;>
      simp only [insertFirst, found, NatIndex.find?_insert, if_pos rfl]
  · cases found : index.find? key <;>
      simp only [insertFirst, found, NatIndex.find?_insert, if_neg same] <;>
      cases index.find? query <;> rfl

theorem insertFirst_find_occupied {α : Type} (index : NatIndex α) (key query : Nat)
    (value previous : α) (occupied : index.find? query = some previous) :
    (insertFirst index key value).find? query = some previous := by
  rw [insertFirst_find, occupied]

theorem insertFirst_find_different {α : Type} (index : NatIndex α) (key query : Nat)
    (value : α) (different : query ≠ key) :
    (insertFirst index key value).find? query = index.find? query := by
  rw [insertFirst_find]
  cases index.find? query <;> simp only [if_neg different]

private theorem index_eq_id {left right : FuncId} (same : left.index = right.index) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- An arbitrary seed takes priority over the first raw source occurrence.
    This keeps decode failures occupied rather than searching for a later body. -/
theorem prepareSourceFrom_statuses (source : List Function) (statuses : NatIndex (D Unit))
    (declarations : NatIndex Unit) (id : FuncId) :
    (prepareSourceFrom source statuses declarations).1.find? id.index =
      match statuses.find? id.index with
      | some previous => some previous
      | none => (source.find? (fun function => function.id == id)).map
          (fun function => function.blocks.map (fun _ => ())) := by
  induction source generalizing statuses declarations with
  | nil =>
    simp only [prepareSourceFrom, List.find?]
    cases statuses.find? id.index <;> rfl
  | cons function rest ih =>
    change (prepareSourceFrom rest
      (insertFirst statuses function.id.index (function.blocks.map (fun _ => ())))
      (if function.isDeclaration then declarations.insert function.id.index () else declarations)).1.find? id.index = _
    rw [ih, insertFirst_find]
    by_cases same : function.id = id
    · have sameIndex : id.index = function.id.index := (congrArg FuncId.index same).symm
      have here : (function.id == id) = true := decide_eq_true same
      cases found : statuses.find? id.index <;>
        simp only [found, if_pos sameIndex, List.find?, here, if_true, Option.map]
    · have different : id.index ≠ function.id.index := fun equal => same (index_eq_id equal.symm)
      have absent : (function.id == id) = false := decide_eq_false same
      cases found : statuses.find? id.index <;>
        simp only [found, if_neg different, List.find?, absent, Bool.false_eq_true, if_false]

/-- The declaration view is an OR over ALL raw rows, independently of which
    same-key source status or executable body wins. Existing seed membership
    is retained even when no source declaration exists. -/
theorem prepareSourceFrom_declarations (source : List Function) (statuses : NatIndex (D Unit))
    (declarations : NatIndex Unit) (id : FuncId) :
    (prepareSourceFrom source statuses declarations).2.contains id.index =
      (declarations.contains id.index || source.any (fun function => function.id == id && function.isDeclaration)) := by
  induction source generalizing statuses declarations with
  | nil => simp only [prepareSourceFrom, List.any_nil, Bool.or_false]
  | cons function rest ih =>
    change (prepareSourceFrom rest
      (insertFirst statuses function.id.index (function.blocks.map (fun _ => ())))
      (if function.isDeclaration then declarations.insert function.id.index () else declarations)).2.contains id.index = _
    rw [ih]
    by_cases same : function.id = id
    · have sameIndex : id.index = function.id.index := (congrArg FuncId.index same).symm
      have here : (function.id == id) = true := decide_eq_true same
      cases declared : function.isDeclaration <;>
        simp only [declared, Bool.false_eq_true, if_false, if_true, List.any_cons, here,
          Bool.true_and, Bool.false_or, Bool.true_or, Bool.or_true,
          NatIndex.contains, NatIndex.find?_insert, if_pos sameIndex, Option.isSome]
    · have different : id.index ≠ function.id.index := fun equal => same (index_eq_id equal.symm)
      have absent : (function.id == id) = false := decide_eq_false same
      cases declared : function.isDeclaration <;>
        simp only [declared, Bool.false_eq_true, if_false, if_true, List.any_cons, absent,
          Bool.false_and, Bool.false_or, NatIndex.contains, NatIndex.find?_insert, if_neg different]

/-- First retained executable conversion in source order, with ANY occupied
    seed result (including an error) taking priority over all incoming rows. -/
theorem prepareDefsFrom_find (definitions : List (FuncId × D EvalFunction))
    (seed : NatIndex (D EvalFunction)) (id : FuncId) :
    (prepareDefsFrom definitions seed).find? id.index =
      match seed.find? id.index with
      | some previous => some previous
      | none => (definitions.find? (fun row => row.fst == id)).map Prod.snd := by
  induction definitions generalizing seed with
  | nil =>
    simp only [prepareDefsFrom, List.find?]
    cases seed.find? id.index <;> rfl
  | cons row rest ih =>
    rcases row with ⟨key, result⟩
    change (prepareDefsFrom rest (insertFirst seed key.index result)).find? id.index = _
    rw [ih, insertFirst_find]
    by_cases same : key = id
    · have sameIndex : id.index = key.index := (congrArg FuncId.index same).symm
      have here : (key == id) = true := decide_eq_true same
      cases found : seed.find? id.index <;>
        simp only [found, if_pos sameIndex, List.find?, here, if_true, Option.map]
    · have different : id.index ≠ key.index := fun equal => same (index_eq_id equal.symm)
      have absent : (key == id) = false := decide_eq_false same
      cases found : seed.find? id.index <;>
        simp only [found, if_neg different, List.find?, absent, Bool.false_eq_true, if_false]

theorem sourceStatuses_prepare (source : List Function)
    (definitions : List (FuncId × D EvalFunction)) (id : FuncId) :
    (prepare source definitions).sourceStatuses.find? id.index =
      (source.find? (fun function => function.id == id)).map
        (fun function => function.blocks.map (fun _ => ())) := by
  change (prepareSourceFrom source NatIndex.empty NatIndex.empty).1.find? id.index = _
  rw [prepareSourceFrom_statuses, NatIndex.find?_empty]

theorem executables_prepare (source : List Function)
    (definitions : List (FuncId × D EvalFunction)) (id : FuncId) :
    (prepare source definitions).executables.find? id.index =
      (definitions.find? (fun row => row.fst == id)).map Prod.snd := by
  change (prepareDefsFrom definitions NatIndex.empty).find? id.index = _
  rw [prepareDefsFrom_find, NatIndex.find?_empty]

-- Select constructive lowering only for the two original optional executable
-- matches below. The original term syntax passes through unchanged on legacy.
syntax (name := lookupPropsOriginalDenseSyntax) "lookupPropsOriginalDenseTerm " term : term

@[term_elab lookupPropsOriginalDenseSyntax]
private def lookupPropsOriginalElabDenseTerm : Lean.Elab.Term.TermElab :=
  fun stx expectedType? =>
    Lean.withOptions (fun options => options.setBool `backward.match.sparseCases false) do
      Lean.Elab.Term.elabTerm stx[1] expectedType?

macro "lookupPropsOriginalDense " value:term : term => do
  if Lean.versionString == "4.8.0" then pure value
  else if Lean.versionString == "4.30.0-rc2" then
    `(lookupPropsOriginalDenseTerm $value)
  else Lean.Macro.throwError "unsupported compiler for original lookup matcher lowering"

-- Modern canonical types below are the complete accepted original Exprs.
-- Their binder names are source data, not reconstructed or normalized fields.
private def lookupPropsRequireClosedDependencies (expression : Lean.Expr) :
    Lean.Elab.Command.CommandElabM Unit := do
  if expression.hasMVar || expression.hasFVar || expression.hasLooseBVars then
    throwError "original declaration expression must be closed"
  let environment ← Lean.getEnv
  for dependency in expression.getUsedConstants do
    unless environment.contains dependency do
      throwError m!"original declaration dependency absent: {dependency}"

private def lookupPropsAddExactOriginalDef (originalName : Lean.Name)
    (originalType originalValue : Lean.Expr) : Lean.Elab.Command.CommandElabM Unit := do
  if (← Lean.getEnv).contains originalName then
    throwError m!"original helper declaration already exists: {originalName}"
  lookupPropsRequireClosedDependencies originalType
  lookupPropsRequireClosedDependencies originalValue
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile (.defnDecl {
    name := originalName
    levelParams := [`u_1]
    type := originalType
    value := originalValue
    hints := .abbrev
    safety := .safe })

private def lookupPropsAddExactOriginalTheorem (originalName : Lean.Name)
    (originalType : Lean.Expr) (proofSyntax : Lean.Syntax) :
    Lean.Elab.Command.CommandElabM Unit := do
  if (← Lean.getEnv).contains originalName then
    throwError m!"original canonical declaration already exists: {originalName}"
  lookupPropsRequireClosedDependencies originalType
  let declaration ← Lean.Elab.Command.liftTermElabM do
    Lean.Elab.Term.withDeclName originalName do
      Lean.Elab.Term.withoutErrToSorry do
        let value ← Lean.Elab.Term.elabTermEnsuringType proofSyntax
          (some originalType) (catchExPostpone := false)
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        let value ← Lean.instantiateMVars value
        if value.hasMVar || value.hasFVar || value.hasLooseBVars then
          throwError "original canonical proof must be closed"
        if value.getUsedConstants.contains `sorryAx then
          throwError "original canonical proof contains sorryAx"
        let declaration := Lean.Declaration.thmDecl {
          name := originalName
          levelParams := []
          type := originalType
          value := value }
        Lean.Elab.Term.ensureNoUnassignedMVars declaration
        pure declaration
  -- Check actual proof constants after ordinary elaboration, including helpers
  -- created by that proof. No original declaration is replaced in the env.
  match declaration with
  | .thmDecl info => lookupPropsRequireClosedDependencies info.value
  | _ => throwError "expected one original theorem declaration"
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile declaration

elab "lookupPropsOriginalFunctionCanonical " original:command : command => do
  if Lean.versionString == "4.8.0" then
    Lean.Elab.Command.elabCommand original
  else if Lean.versionString == "4.30.0-rc2" then
    let originalType0 : Lean.Expr := (Lean.Expr.forallE
  `motive
  (Lean.Expr.forallE
    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1795)
    (Lean.Expr.app
      (Lean.Expr.const `Option [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.sort (Lean.Level.param `u_1))
    (Lean.BinderInfo.default))
  (Lean.Expr.forallE
    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1795)
    (Lean.Expr.app
      (Lean.Expr.const `Option [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.forallE
      `h_1
      (Lean.Expr.forallE
        (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1813)
        (Lean.Expr.const `TrustIr.FuncId [])
        (Lean.Expr.forallE
          `function
          (Lean.Expr.const `TrustIr.EvalFunction [])
          (Lean.Expr.app
            (Lean.Expr.bvar 3)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Option.some [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.FuncId []))
                  (Lean.Expr.app
                    (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.EvalFunction []))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.FuncId []))
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction [])))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIrEval.DecodeError []))
                    (Lean.Expr.const `TrustIr.EvalFunction []))
                  (Lean.Expr.bvar 0)))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.Expr.forallE
        `h_2
        (Lean.Expr.forallE
          (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1819)
          (Lean.Expr.app
            (Lean.Expr.const `Option [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIr.FuncId []))
              (Lean.Expr.app
                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                (Lean.Expr.const `TrustIr.EvalFunction []))))
          (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
          (Lean.BinderInfo.default))
        (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 2))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    let originalValue0 : Lean.Expr := (Lean.Expr.lam
  `motive
  (Lean.Expr.forallE
    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1795)
    (Lean.Expr.app
      (Lean.Expr.const `Option [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.sort (Lean.Level.param `u_1))
    (Lean.BinderInfo.default))
  (Lean.Expr.lam
    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1795)
    (Lean.Expr.app
      (Lean.Expr.const `Option [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.lam
      `h_1
      (Lean.Expr.forallE
        (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1813)
        (Lean.Expr.const `TrustIr.FuncId [])
        (Lean.Expr.forallE
          `function
          (Lean.Expr.const `TrustIr.EvalFunction [])
          (Lean.Expr.app
            (Lean.Expr.bvar 3)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Option.some [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.FuncId []))
                  (Lean.Expr.app
                    (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.EvalFunction []))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.FuncId []))
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction [])))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIrEval.DecodeError []))
                    (Lean.Expr.const `TrustIr.EvalFunction []))
                  (Lean.Expr.bvar 0)))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.Expr.lam
        `h_2
        (Lean.Expr.forallE
          (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1819)
          (Lean.Expr.app
            (Lean.Expr.const `Option [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIr.FuncId []))
              (Lean.Expr.app
                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                (Lean.Expr.const `TrustIr.EvalFunction []))))
          (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Option.casesOn [Lean.Level.param `u_1, Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.FuncId []))
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction []))))
                (Lean.Expr.lam
                  `x
                  (Lean.Expr.app
                    (Lean.Expr.const `Option [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.FuncId []))
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.EvalFunction []))))
                  (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                  (Lean.BinderInfo.default)))
              (Lean.Expr.bvar 2))
            (Lean.Expr.app
              (Lean.Expr.bvar 0)
              (Lean.Expr.app
                (Lean.Expr.const `Option.none [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.FuncId []))
                  (Lean.Expr.app
                    (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.EvalFunction []))))))
          (Lean.Expr.lam
            (Lean.Name.num `val.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1821)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIr.FuncId []))
              (Lean.Expr.app
                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                (Lean.Expr.const `TrustIr.EvalFunction [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod.casesOn [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.FuncId []))
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction [])))
                  (Lean.Expr.lam
                    `x
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.FuncId []))
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.EvalFunction [])))
                    (Lean.Expr.app
                      (Lean.Expr.bvar 5)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Option.some [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction []))))
                        (Lean.Expr.bvar 0)))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.bvar 0))
              (Lean.Expr.lam
                (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1822)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.lam
                  (Lean.Name.num `snd.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 1823)
                  (Lean.Expr.app
                    (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.EvalFunction []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `Except.casesOn
                                [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIrEval.DecodeError []))
                            (Lean.Expr.const `TrustIr.EvalFunction []))
                          (Lean.Expr.lam
                            `x
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction []))
                            (Lean.Expr.app
                              (Lean.Expr.bvar 7)
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Option.some [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.FuncId []))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.EvalFunction []))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `TrustIr.FuncId []))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                        (Lean.Expr.const `TrustIr.EvalFunction [])))
                                    (Lean.Expr.bvar 2))
                                  (Lean.Expr.bvar 0))))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.bvar 0))
                      (Lean.Expr.lam
                        (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10095) "TrustIr") "Proofs") "DecodedFunctionLookupProps") "_hyg") 1824)
                        (Lean.Expr.const `TrustIrEval.DecodeError [])
                        (Lean.Expr.app
                          (Lean.Expr.bvar 4)
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Option.some [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.FuncId []))
                                (Lean.Expr.app
                                  (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.EvalFunction []))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `TrustIr.FuncId []))
                                  (Lean.Expr.app
                                    (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                    (Lean.Expr.const `TrustIr.EvalFunction [])))
                                (Lean.Expr.bvar 2))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `TrustIrEval.DecodeError []))
                                  (Lean.Expr.const `TrustIr.EvalFunction []))
                                (Lean.Expr.bvar 0)))))
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.lam
                      (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedFunctionLookupProps") "_hyg") 1825)
                      (Lean.Expr.const `TrustIr.EvalFunction [])
                      (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 5) (Lean.Expr.bvar 2)) (Lean.Expr.bvar 0))
                      (Lean.BinderInfo.default)))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default)))
            (Lean.BinderInfo.default)))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    lookupPropsAddExactOriginalDef `TrustIrEval.FunctionLookup.findFunction_prepare.match_1 originalType0 originalValue0
    let canonicalType : Lean.Expr := (Lean.Expr.forallE
  `source
  (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
  (Lean.Expr.forallE
    `definitions
    (Lean.Expr.app
      (Lean.Expr.const `List [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.forallE
      `id
      (Lean.Expr.const `TrustIr.FuncId [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `TrustIrEval.FunctionLookup.findFunction [])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.FunctionLookup.prepare []) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.bvar 0)))
        (Lean.Expr.mdata
          { entries := [(`save_info, Lean.DataValue.ofBool true)] }
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `TrustIrEval.FunctionLookup.findFunction_prepare.match_1
                    [Lean.Level.succ (Lean.Level.zero)])
                  (Lean.Expr.lam
                    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 30402171) "_hygCtx") "_hyg") 48)
                    (Lean.Expr.app
                      (Lean.Expr.const `Option [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.FuncId []))
                        (Lean.Expr.app
                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.EvalFunction []))))
                    (Lean.Expr.app
                      (Lean.Expr.const `Option [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction []))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `List.find? [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.FuncId []))
                        (Lean.Expr.app
                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.EvalFunction []))))
                    (Lean.Expr.lam
                      `row
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.FuncId []))
                        (Lean.Expr.app
                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.EvalFunction [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `BEq.beq [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `instBEqOfDecidableEq [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.const `TrustIr.instDecidableEqFuncId [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod.fst [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.EvalFunction [])))
                            (Lean.Expr.bvar 0)))
                        (Lean.Expr.bvar 1))
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.lam
                (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 30402171) "_hygCtx") "_hyg") 66)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.lam
                  `function
                  (Lean.Expr.const `TrustIr.EvalFunction [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Option.some [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction []))
                    (Lean.Expr.bvar 0))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam
              (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 30402171) "_hygCtx") "_hyg") 72)
              (Lean.Expr.app
                (Lean.Expr.const `Option [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.FuncId []))
                  (Lean.Expr.app
                    (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.EvalFunction []))))
              (Lean.Expr.app
                (Lean.Expr.const `Option.none [Lean.Level.zero])
                (Lean.Expr.const `TrustIr.EvalFunction []))
              (Lean.BinderInfo.default)))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    let originalFunctionMatcher := Lean.mkIdent `TrustIrEval.FunctionLookup.findFunction_prepare.match_1
    let proofSyntax ← `(term| by
      intro source definitions id
      unfold findFunction
      rw [executables_prepare]
      generalize (definitions.find? (fun row => row.fst == id)) = selected
      induction selected using $originalFunctionMatcher:ident
      · rename_i key function
        rfl
      · rename_i remaining
        cases remaining with
        | none => rfl
        | some row =>
          rcases row with ⟨key, result⟩
          cases result <;> rfl
    )
    lookupPropsAddExactOriginalTheorem `TrustIrEval.FunctionLookup.findFunction_prepare canonicalType proofSyntax
  else throwError "unsupported compiler for original canonical type preservation"


lookupPropsOriginalFunctionCanonical
/-- EXACT original list query, including first-error occupancy. -/
theorem findFunction_prepare (source : List Function)
    (definitions : List (FuncId × D EvalFunction)) (id : FuncId) :
    findFunction (prepare source definitions) id =
      match definitions.find? (fun row => row.fst == id) with
      | some (_, Except.ok function) => some function
      | _ => none := by
  unfold findFunction
  rw [executables_prepare]
  cases found : definitions.find? (fun row => row.fst == id) with
  | none => rfl
  | some row =>
    rcases row with ⟨key, result⟩
    cases result <;> rfl

/-- EXACT original any-declaration query; it is NOT a first-row property. -/
theorem isDeclared_prepare (source : List Function)
    (definitions : List (FuncId × D EvalFunction)) (id : FuncId) :
    isDeclared (prepare source definitions) id =
      source.any (fun function => function.id == id && function.isDeclaration) := by
  change (prepareSourceFrom source NatIndex.empty NatIndex.empty).2.contains id.index = _
  rw [prepareSourceFrom_declarations]
  rfl

-- The missing original blocks eliminator is added only after the canonical
-- theorem type has elaborated, so its name is not reserved during type matching.
-- Type and value below are the complete accepted legacy Exprs, not a type alias.
elab "lookupPropsOriginalAddBlocksMatcher" : tactic => do
  if Lean.versionString != "4.30.0-rc2" then
    throwError "original blocks matcher addition is modern-only"
  let originalName := `TrustIrEval.FunctionLookup.findError_prepare.match_2
  if (← Lean.getEnv).contains originalName then
    throwError "original blocks matcher already exists; refusing declaration replacement"
  let originalType : Lean.Expr :=
    Lean.Expr.forallE
      `motive
      (Lean.Expr.forallE
        (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 2941)
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
            (Lean.Expr.const `TrustIrEval.DecodeError []))
          (Lean.Expr.app
            (Lean.Expr.const `List [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIr.BlockId []))
              (Lean.Expr.const `TrustIr.BasicBlock []))))
        (Lean.Expr.sort (Lean.Level.param `u_1))
        (Lean.BinderInfo.default))
      (Lean.Expr.forallE
        (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 2941)
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
            (Lean.Expr.const `TrustIrEval.DecodeError []))
          (Lean.Expr.app
            (Lean.Expr.const `List [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIr.BlockId []))
              (Lean.Expr.const `TrustIr.BasicBlock []))))
        (Lean.Expr.forallE
          `h_1
          (Lean.Expr.forallE
            `feature
            (Lean.Expr.const `String [])
            (Lean.Expr.app
              (Lean.Expr.bvar 2)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIrEval.DecodeError []))
                  (Lean.Expr.app
                    (Lean.Expr.const `List [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.BlockId []))
                      (Lean.Expr.const `TrustIr.BasicBlock []))))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))
            (Lean.BinderInfo.default))
          (Lean.Expr.forallE
            `h_2
            (Lean.Expr.forallE
              `message
              (Lean.Expr.const `String [])
              (Lean.Expr.app
                (Lean.Expr.bvar 3)
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIrEval.DecodeError []))
                    (Lean.Expr.app
                      (Lean.Expr.const `List [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.BlockId []))
                        (Lean.Expr.const `TrustIr.BasicBlock []))))
                  (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))
              (Lean.BinderInfo.default))
            (Lean.Expr.forallE
              `h_3
              (Lean.Expr.forallE
                (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedFunctionLookupProps") "_hyg") 3018)
                (Lean.Expr.app
                  (Lean.Expr.const `List [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.BlockId []))
                    (Lean.Expr.const `TrustIr.BasicBlock [])))
                (Lean.Expr.app
                  (Lean.Expr.bvar 4)
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                      (Lean.Expr.app
                        (Lean.Expr.const `List [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.BlockId []))
                          (Lean.Expr.const `TrustIr.BasicBlock []))))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 3))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default)
  let originalValue : Lean.Expr :=
    Lean.Expr.lam
      `motive
      (Lean.Expr.forallE
        (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 2941)
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
            (Lean.Expr.const `TrustIrEval.DecodeError []))
          (Lean.Expr.app
            (Lean.Expr.const `List [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIr.BlockId []))
              (Lean.Expr.const `TrustIr.BasicBlock []))))
        (Lean.Expr.sort (Lean.Level.param `u_1))
        (Lean.BinderInfo.default))
      (Lean.Expr.lam
        (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 2941)
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
            (Lean.Expr.const `TrustIrEval.DecodeError []))
          (Lean.Expr.app
            (Lean.Expr.const `List [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIr.BlockId []))
              (Lean.Expr.const `TrustIr.BasicBlock []))))
        (Lean.Expr.lam
          `h_1
          (Lean.Expr.forallE
            `feature
            (Lean.Expr.const `String [])
            (Lean.Expr.app
              (Lean.Expr.bvar 2)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIrEval.DecodeError []))
                  (Lean.Expr.app
                    (Lean.Expr.const `List [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.BlockId []))
                      (Lean.Expr.const `TrustIr.BasicBlock []))))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))
            (Lean.BinderInfo.default))
          (Lean.Expr.lam
            `h_2
            (Lean.Expr.forallE
              `message
              (Lean.Expr.const `String [])
              (Lean.Expr.app
                (Lean.Expr.bvar 3)
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIrEval.DecodeError []))
                    (Lean.Expr.app
                      (Lean.Expr.const `List [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.BlockId []))
                        (Lean.Expr.const `TrustIr.BasicBlock []))))
                  (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))
              (Lean.BinderInfo.default))
            (Lean.Expr.lam
              `h_3
              (Lean.Expr.forallE
                (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedFunctionLookupProps") "_hyg") 3018)
                (Lean.Expr.app
                  (Lean.Expr.const `List [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.BlockId []))
                    (Lean.Expr.const `TrustIr.BasicBlock [])))
                (Lean.Expr.app
                  (Lean.Expr.bvar 4)
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                      (Lean.Expr.app
                        (Lean.Expr.const `List [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.BlockId []))
                          (Lean.Expr.const `TrustIr.BasicBlock []))))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Except.casesOn [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIrEval.DecodeError []))
                        (Lean.Expr.app
                          (Lean.Expr.const `List [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.BlockId []))
                            (Lean.Expr.const `TrustIr.BasicBlock []))))
                      (Lean.Expr.lam
                        `x
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIrEval.DecodeError []))
                          (Lean.Expr.app
                            (Lean.Expr.const `List [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.BlockId []))
                              (Lean.Expr.const `TrustIr.BasicBlock []))))
                        (Lean.Expr.app (Lean.Expr.bvar 5) (Lean.Expr.bvar 0))
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.lam
                    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10095) "TrustIr") "Proofs") "DecodedFunctionLookupProps") "_hyg") 3106)
                    (Lean.Expr.const `TrustIrEval.DecodeError [])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `TrustIrEval.DecodeError.casesOn [Lean.Level.param `u_1])
                            (Lean.Expr.lam
                              `x
                              (Lean.Expr.const `TrustIrEval.DecodeError [])
                              (Lean.Expr.app
                                (Lean.Expr.bvar 6)
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `TrustIrEval.DecodeError []))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `List [Lean.Level.zero])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `TrustIr.BlockId []))
                                        (Lean.Expr.const `TrustIr.BasicBlock []))))
                                  (Lean.Expr.bvar 0)))
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.bvar 0))
                        (Lean.Expr.lam
                          (Lean.Name.num `feature.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3108)
                          (Lean.Expr.const `String [])
                          (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.lam
                        (Lean.Name.num `msg.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3109)
                        (Lean.Expr.const `String [])
                        (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                        (Lean.BinderInfo.default)))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.lam
                  (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedFunctionLookupProps") "_hyg") 3107)
                  (Lean.Expr.app
                    (Lean.Expr.const `List [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.BlockId []))
                      (Lean.Expr.const `TrustIr.BasicBlock [])))
                  (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
                  (Lean.BinderInfo.default)))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default)
  Lean.addAndCompile (.defnDecl {
    name := originalName
    levelParams := [`u_1]
    type := originalType
    value := originalValue
    hints := .abbrev
    safety := .safe })

-- Restore the original full Option Function eliminator on the modern pin.
-- Its actual canonical consumer is the complete findError_prepare proof below.
run_cmd do
  if Lean.versionString == "4.8.0" then pure ()
  else if Lean.versionString == "4.30.0-rc2" then
    let originalName := Lean.mkIdent
      (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "findError_prepare") "match_3")
    let originalUniverse := Lean.mkIdent
      (Lean.Name.str Lean.Name.anonymous "u_1")
    let originalLevel ← `(level| $originalUniverse:ident)
    Lean.Elab.Command.elabCommand (← `(command|
      def $originalName:ident.{$originalUniverse:ident}
          (motive : Option Function → Sort $originalLevel:level)
          (selected : Option Function)
          (h_1 : (function : Function) → motive (some function))
          (h_2 : Unit → motive none) : motive selected :=
        Option.casesOn selected (h_2 ()) (fun function => h_1 function)))
  else throwError "unsupported compiler for original error lookup matcher"

elab "lookupPropsOriginalErrorCanonical " original:command : command => do
  if Lean.versionString == "4.8.0" then
    Lean.Elab.Command.elabCommand original
  else if Lean.versionString == "4.30.0-rc2" then
    let originalType0 : Lean.Expr := (Lean.Expr.forallE
  `motive
  (Lean.Expr.forallE
    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3039)
    (Lean.Expr.app
      (Lean.Expr.const `Option [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.sort (Lean.Level.param `u_1))
    (Lean.BinderInfo.default))
  (Lean.Expr.forallE
    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3039)
    (Lean.Expr.app
      (Lean.Expr.const `Option [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.forallE
      `h_1
      (Lean.Expr.forallE
        (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3062)
        (Lean.Expr.const `TrustIr.FuncId [])
        (Lean.Expr.forallE
          `message
          (Lean.Expr.const `String [])
          (Lean.Expr.app
            (Lean.Expr.bvar 3)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Option.some [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.FuncId []))
                  (Lean.Expr.app
                    (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.EvalFunction []))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.FuncId []))
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction [])))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIrEval.DecodeError []))
                    (Lean.Expr.const `TrustIr.EvalFunction []))
                  (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.Expr.forallE
        `h_2
        (Lean.Expr.forallE
          (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3086)
          (Lean.Expr.const `TrustIr.FuncId [])
          (Lean.Expr.forallE
            `feature
            (Lean.Expr.const `String [])
            (Lean.Expr.app
              (Lean.Expr.bvar 4)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Option.some [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.FuncId []))
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction []))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.FuncId []))
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.EvalFunction [])))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                      (Lean.Expr.const `TrustIr.EvalFunction []))
                    (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.forallE
          `h_3
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3096)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app
                  (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                  (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
            (Lean.BinderInfo.default))
          (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 3))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    let originalValue0 : Lean.Expr := (Lean.Expr.lam
  `motive
  (Lean.Expr.forallE
    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3039)
    (Lean.Expr.app
      (Lean.Expr.const `Option [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.sort (Lean.Level.param `u_1))
    (Lean.BinderInfo.default))
  (Lean.Expr.lam
    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3039)
    (Lean.Expr.app
      (Lean.Expr.const `Option [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.lam
      `h_1
      (Lean.Expr.forallE
        (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3062)
        (Lean.Expr.const `TrustIr.FuncId [])
        (Lean.Expr.forallE
          `message
          (Lean.Expr.const `String [])
          (Lean.Expr.app
            (Lean.Expr.bvar 3)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Option.some [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.FuncId []))
                  (Lean.Expr.app
                    (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.EvalFunction []))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.FuncId []))
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction [])))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIrEval.DecodeError []))
                    (Lean.Expr.const `TrustIr.EvalFunction []))
                  (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.Expr.lam
        `h_2
        (Lean.Expr.forallE
          (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3086)
          (Lean.Expr.const `TrustIr.FuncId [])
          (Lean.Expr.forallE
            `feature
            (Lean.Expr.const `String [])
            (Lean.Expr.app
              (Lean.Expr.bvar 4)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Option.some [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.FuncId []))
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction []))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.FuncId []))
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.EvalFunction [])))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                      (Lean.Expr.const `TrustIr.EvalFunction []))
                    (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.lam
          `h_3
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3096)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app
                  (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                  (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Option.casesOn [Lean.Level.param `u_1, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.FuncId []))
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.EvalFunction []))))
                  (Lean.Expr.lam
                    `x
                    (Lean.Expr.app
                      (Lean.Expr.const `Option [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.FuncId []))
                        (Lean.Expr.app
                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.EvalFunction []))))
                    (Lean.Expr.app (Lean.Expr.bvar 5) (Lean.Expr.bvar 0))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.bvar 3))
              (Lean.Expr.app
                (Lean.Expr.bvar 0)
                (Lean.Expr.app
                  (Lean.Expr.const `Option.none [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.FuncId []))
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction []))))))
            (Lean.Expr.lam
              (Lean.Name.num `val.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3099)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app
                  (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                  (Lean.Expr.const `TrustIr.EvalFunction [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod.casesOn [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.FuncId []))
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.EvalFunction [])))
                    (Lean.Expr.lam
                      `x
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.FuncId []))
                        (Lean.Expr.app
                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.EvalFunction [])))
                      (Lean.Expr.app
                        (Lean.Expr.bvar 6)
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Option.some [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.EvalFunction []))))
                          (Lean.Expr.bvar 0)))
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.bvar 0))
                (Lean.Expr.lam
                  (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3100)
                  (Lean.Expr.const `TrustIr.FuncId [])
                  (Lean.Expr.lam
                    (Lean.Name.num `snd.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3101)
                    (Lean.Expr.app
                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.EvalFunction []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `Except.casesOn
                                  [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIrEval.DecodeError []))
                              (Lean.Expr.const `TrustIr.EvalFunction []))
                            (Lean.Expr.lam
                              `x
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.EvalFunction []))
                              (Lean.Expr.app
                                (Lean.Expr.bvar 8)
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Option.some [Lean.Level.zero])
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `TrustIr.FuncId []))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                        (Lean.Expr.const `TrustIr.EvalFunction []))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `TrustIr.FuncId []))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                          (Lean.Expr.const `TrustIr.EvalFunction [])))
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.bvar 0))))
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.bvar 0))
                        (Lean.Expr.lam
                          (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10095) "TrustIr") "Proofs") "DecodedFunctionLookupProps") "_hyg") 3102)
                          (Lean.Expr.const `TrustIrEval.DecodeError [])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `TrustIrEval.DecodeError.casesOn [Lean.Level.param `u_1])
                                  (Lean.Expr.lam
                                    `x
                                    (Lean.Expr.const `TrustIrEval.DecodeError [])
                                    (Lean.Expr.app
                                      (Lean.Expr.bvar 9)
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Option.some [Lean.Level.zero])
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                              (Lean.Expr.const `TrustIr.FuncId []))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                              (Lean.Expr.const `TrustIr.EvalFunction []))))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                                (Lean.Expr.const `TrustIr.FuncId []))
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                                (Lean.Expr.const `TrustIr.EvalFunction [])))
                                            (Lean.Expr.bvar 3))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                                                (Lean.Expr.const `TrustIrEval.DecodeError []))
                                              (Lean.Expr.const `TrustIr.EvalFunction []))
                                            (Lean.Expr.bvar 0)))))
                                    (Lean.BinderInfo.default)))
                                (Lean.Expr.bvar 0))
                              (Lean.Expr.lam
                                (Lean.Name.num `feature.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3104)
                                (Lean.Expr.const `String [])
                                (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 6) (Lean.Expr.bvar 3)) (Lean.Expr.bvar 0))
                                (Lean.BinderInfo.default)))
                            (Lean.Expr.lam
                              (Lean.Name.num `msg.«_@».TrustIr.Proofs.DecodedFunctionLookupProps._hyg 3105)
                              (Lean.Expr.const `String [])
                              (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 7) (Lean.Expr.bvar 3)) (Lean.Expr.bvar 0))
                              (Lean.BinderInfo.default)))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.lam
                        (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedFunctionLookupProps") "_hyg") 3103)
                        (Lean.Expr.const `TrustIr.EvalFunction [])
                        (Lean.Expr.app
                          (Lean.Expr.bvar 4)
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Option.some [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.FuncId []))
                                (Lean.Expr.app
                                  (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.EvalFunction []))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `TrustIr.FuncId []))
                                  (Lean.Expr.app
                                    (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                    (Lean.Expr.const `TrustIr.EvalFunction [])))
                                (Lean.Expr.bvar 2))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `TrustIrEval.DecodeError []))
                                  (Lean.Expr.const `TrustIr.EvalFunction []))
                                (Lean.Expr.bvar 0)))))
                        (Lean.BinderInfo.default)))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.default)))
              (Lean.BinderInfo.default)))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    lookupPropsAddExactOriginalDef `TrustIrEval.FunctionLookup.findError_prepare.match_1 originalType0 originalValue0
    let originalType1 : Lean.Expr := (Lean.Expr.forallE
  `motive
  (Lean.Expr.forallE
    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 57)
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
        (Lean.Expr.const `TrustIrEval.DecodeError []))
      (Lean.Expr.app
        (Lean.Expr.const `List [Lean.Level.zero])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
            (Lean.Expr.const `TrustIr.BlockId []))
          (Lean.Expr.const `TrustIr.BasicBlock []))))
    (Lean.Expr.sort (Lean.Level.param `u_1))
    (Lean.BinderInfo.default))
  (Lean.Expr.forallE
    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 57)
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
        (Lean.Expr.const `TrustIrEval.DecodeError []))
      (Lean.Expr.app
        (Lean.Expr.const `List [Lean.Level.zero])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
            (Lean.Expr.const `TrustIr.BlockId []))
          (Lean.Expr.const `TrustIr.BasicBlock []))))
    (Lean.Expr.forallE
      `h_1
      (Lean.Expr.forallE
        `feature
        (Lean.Expr.const `String [])
        (Lean.Expr.app
          (Lean.Expr.bvar 2)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))
        (Lean.BinderInfo.default))
      (Lean.Expr.forallE
        `h_2
        (Lean.Expr.forallE
          `message
          (Lean.Expr.const `String [])
          (Lean.Expr.app
            (Lean.Expr.bvar 3)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `TrustIrEval.DecodeError []))
                (Lean.Expr.app
                  (Lean.Expr.const `List [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.BlockId []))
                    (Lean.Expr.const `TrustIr.BasicBlock []))))
              (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))
          (Lean.BinderInfo.default))
        (Lean.Expr.forallE
          `h_3
          (Lean.Expr.forallE
            (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@»._internal 0) "TrustIr") "Proofs") "DecodedFunctionLookupProps") 1775725367) "_hygCtx") "_hyg") 128)
            (Lean.Expr.app
              (Lean.Expr.const `List [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `TrustIr.BlockId []))
                (Lean.Expr.const `TrustIr.BasicBlock [])))
            (Lean.Expr.app
              (Lean.Expr.bvar 4)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIrEval.DecodeError []))
                  (Lean.Expr.app
                    (Lean.Expr.const `List [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.BlockId []))
                      (Lean.Expr.const `TrustIr.BasicBlock []))))
                (Lean.Expr.bvar 0)))
            (Lean.BinderInfo.default))
          (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 3))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    let originalValue1 : Lean.Expr := (Lean.Expr.lam
  `motive
  (Lean.Expr.forallE
    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 57)
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
        (Lean.Expr.const `TrustIrEval.DecodeError []))
      (Lean.Expr.app
        (Lean.Expr.const `List [Lean.Level.zero])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
            (Lean.Expr.const `TrustIr.BlockId []))
          (Lean.Expr.const `TrustIr.BasicBlock []))))
    (Lean.Expr.sort (Lean.Level.param `u_1))
    (Lean.BinderInfo.default))
  (Lean.Expr.lam
    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 57)
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
        (Lean.Expr.const `TrustIrEval.DecodeError []))
      (Lean.Expr.app
        (Lean.Expr.const `List [Lean.Level.zero])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
            (Lean.Expr.const `TrustIr.BlockId []))
          (Lean.Expr.const `TrustIr.BasicBlock []))))
    (Lean.Expr.lam
      `h_1
      (Lean.Expr.forallE
        `feature
        (Lean.Expr.const `String [])
        (Lean.Expr.app
          (Lean.Expr.bvar 2)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))
        (Lean.BinderInfo.default))
      (Lean.Expr.lam
        `h_2
        (Lean.Expr.forallE
          `message
          (Lean.Expr.const `String [])
          (Lean.Expr.app
            (Lean.Expr.bvar 3)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `TrustIrEval.DecodeError []))
                (Lean.Expr.app
                  (Lean.Expr.const `List [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.BlockId []))
                    (Lean.Expr.const `TrustIr.BasicBlock []))))
              (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))
          (Lean.BinderInfo.default))
        (Lean.Expr.lam
          `h_3
          (Lean.Expr.forallE
            (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@»._internal 0) "TrustIr") "Proofs") "DecodedFunctionLookupProps") 1775725367) "_hygCtx") "_hyg") 128)
            (Lean.Expr.app
              (Lean.Expr.const `List [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `TrustIr.BlockId []))
                (Lean.Expr.const `TrustIr.BasicBlock [])))
            (Lean.Expr.app
              (Lean.Expr.bvar 4)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIrEval.DecodeError []))
                  (Lean.Expr.app
                    (Lean.Expr.const `List [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.BlockId []))
                      (Lean.Expr.const `TrustIr.BasicBlock []))))
                (Lean.Expr.bvar 0)))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Except.casesOn [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIrEval.DecodeError []))
                    (Lean.Expr.app
                      (Lean.Expr.const `List [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.BlockId []))
                        (Lean.Expr.const `TrustIr.BasicBlock []))))
                  (Lean.Expr.lam
                    `x
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                      (Lean.Expr.app
                        (Lean.Expr.const `List [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.BlockId []))
                          (Lean.Expr.const `TrustIr.BasicBlock []))))
                    (Lean.Expr.app (Lean.Expr.bvar 5) (Lean.Expr.bvar 0))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.bvar 3))
              (Lean.Expr.lam
                (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@»._internal 0) "TrustIr") "Proofs") "DecodedFunctionLookupProps") 1775725367) "_hygCtx") "_hyg") 224)
                (Lean.Expr.const `TrustIrEval.DecodeError [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.DecodeError.casesOn [Lean.Level.param `u_1])
                        (Lean.Expr.lam
                          `x
                          (Lean.Expr.const `TrustIrEval.DecodeError [])
                          (Lean.Expr.app
                            (Lean.Expr.bvar 6)
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `TrustIrEval.DecodeError []))
                                (Lean.Expr.app
                                  (Lean.Expr.const `List [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.BlockId []))
                                    (Lean.Expr.const `TrustIr.BasicBlock []))))
                              (Lean.Expr.bvar 0)))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.bvar 0))
                    (Lean.Expr.lam
                      (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `feature.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 226)
                      (Lean.Expr.const `String [])
                      (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.lam
                    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `msg.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 227)
                    (Lean.Expr.const `String [])
                    (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                    (Lean.BinderInfo.default)))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam
              (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@»._internal 0) "TrustIr") "Proofs") "DecodedFunctionLookupProps") 1775725367) "_hygCtx") "_hyg") 225)
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock [])))
              (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
              (Lean.BinderInfo.default)))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    lookupPropsAddExactOriginalDef `TrustIrEval.FunctionLookup.findError_prepare.match_4 originalType1 originalValue1
    let originalType2 : Lean.Expr := (Lean.Expr.forallE
  `motive
  (Lean.Expr.forallE
    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 48)
    (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
    (Lean.Expr.sort (Lean.Level.param `u_1))
    (Lean.BinderInfo.default))
  (Lean.Expr.forallE
    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 48)
    (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
    (Lean.Expr.forallE
      `h_1
      (Lean.Expr.forallE
        `function
        (Lean.Expr.const `TrustIrEval.Function [])
        (Lean.Expr.app
          (Lean.Expr.bvar 2)
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Option.some [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
            (Lean.Expr.bvar 0)))
        (Lean.BinderInfo.default))
      (Lean.Expr.forallE
        `h_2
        (Lean.Expr.forallE
          Lean.Name.anonymous
          (Lean.Expr.const `Unit [])
          (Lean.Expr.app
            (Lean.Expr.bvar 3)
            (Lean.Expr.app (Lean.Expr.const `Option.none [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function [])))
          (Lean.BinderInfo.default))
        (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 2))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    let originalValue2 : Lean.Expr := (Lean.Expr.lam
  `motive
  (Lean.Expr.forallE
    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 48)
    (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
    (Lean.Expr.sort (Lean.Level.param `u_1))
    (Lean.BinderInfo.default))
  (Lean.Expr.lam
    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 48)
    (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
    (Lean.Expr.lam
      `h_1
      (Lean.Expr.forallE
        `function
        (Lean.Expr.const `TrustIrEval.Function [])
        (Lean.Expr.app
          (Lean.Expr.bvar 2)
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Option.some [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
            (Lean.Expr.bvar 0)))
        (Lean.BinderInfo.default))
      (Lean.Expr.lam
        `h_2
        (Lean.Expr.forallE
          Lean.Name.anonymous
          (Lean.Expr.const `Unit [])
          (Lean.Expr.app
            (Lean.Expr.bvar 3)
            (Lean.Expr.app (Lean.Expr.const `Option.none [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function [])))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Option.casesOn [Lean.Level.param `u_1, Lean.Level.zero])
                  (Lean.Expr.const `TrustIrEval.Function []))
                (Lean.Expr.lam
                  `x
                  (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
                  (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                  (Lean.BinderInfo.default)))
              (Lean.Expr.bvar 2))
            (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.const `Unit.unit [])))
          (Lean.Expr.lam
            (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `val.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 234)
            (Lean.Expr.const `TrustIrEval.Function [])
            (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
            (Lean.BinderInfo.default)))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    lookupPropsAddExactOriginalDef `TrustIrEval.FunctionLookup.findError_prepare.match_6 originalType2 originalValue2
    let canonicalType : Lean.Expr := (Lean.Expr.forallE
  `source
  (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
  (Lean.Expr.forallE
    `definitions
    (Lean.Expr.app
      (Lean.Expr.const `List [Lean.Level.zero])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
    (Lean.Expr.forallE
      `id
      (Lean.Expr.const `TrustIr.FuncId [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.SemError [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `TrustIrEval.FunctionLookup.findError [])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.FunctionLookup.prepare []) (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.bvar 0)))
        (Lean.Expr.mdata
          { entries := [(`save_info, Lean.DataValue.ofBool true)] }
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `TrustIrEval.FunctionLookup.findError_prepare.match_6
                    [Lean.Level.succ (Lean.Level.zero)])
                  (Lean.Expr.lam
                    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 48)
                    (Lean.Expr.app
                      (Lean.Expr.const `Option [Lean.Level.zero])
                      (Lean.Expr.const `TrustIrEval.Function []))
                    (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.SemError []))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `List.find? [Lean.Level.zero])
                      (Lean.Expr.const `TrustIrEval.Function []))
                    (Lean.Expr.lam
                      `function
                      (Lean.Expr.const `TrustIrEval.Function [])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `BEq.beq [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `instBEqOfDecidableEq [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.const `TrustIr.instDecidableEqFuncId [])))
                          (Lean.Expr.app (Lean.Expr.const `TrustIrEval.Function.id []) (Lean.Expr.bvar 0)))
                        (Lean.Expr.bvar 1))
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.bvar 2)))
              (Lean.Expr.lam
                `function
                (Lean.Expr.const `TrustIrEval.Function [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `TrustIrEval.FunctionLookup.findError_prepare.match_4
                            [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.lam
                            (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 57)
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIrEval.DecodeError []))
                              (Lean.Expr.app
                                (Lean.Expr.const `List [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `TrustIr.BlockId []))
                                  (Lean.Expr.const `TrustIr.BasicBlock []))))
                            (Lean.Expr.app
                              (Lean.Expr.const `Option [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.SemError []))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.app (Lean.Expr.const `TrustIrEval.Function.blocks []) (Lean.Expr.bvar 0)))
                      (Lean.Expr.lam
                        `feature
                        (Lean.Expr.const `String [])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Option.some [Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.SemError []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIr.SemError.unsupported [])
                              (Lean.Expr.const `TrustIr.UnsupportedFeature.interproceduralCall []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `HAppend.hAppend
                                          [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `String []))
                                      (Lean.Expr.const `String []))
                                    (Lean.Expr.const `String []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `instHAppendOfAppend [Lean.Level.zero])
                                      (Lean.Expr.const `String []))
                                    (Lean.Expr.const `instAppendString [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `HAppend.hAppend
                                              [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `String []))
                                          (Lean.Expr.const `String []))
                                        (Lean.Expr.const `String []))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `instHAppendOfAppend [Lean.Level.zero])
                                          (Lean.Expr.const `String []))
                                        (Lean.Expr.const `instAppendString [])))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `HAppend.hAppend
                                                  [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                                (Lean.Expr.const `String []))
                                              (Lean.Expr.const `String []))
                                            (Lean.Expr.const `String []))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `instHAppendOfAppend [Lean.Level.zero])
                                              (Lean.Expr.const `String []))
                                            (Lean.Expr.const `instAppendString [])))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `ToString.toString [Lean.Level.zero])
                                              (Lean.Expr.const `String []))
                                            (Lean.Expr.const `instToStringString []))
                                          (Lean.Expr.lit (Lean.Literal.strVal "function "))))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `ToString.toString [Lean.Level.zero])
                                            (Lean.Expr.const `Nat []))
                                          (Lean.Expr.const `instToStringNat []))
                                        (Lean.Expr.app (Lean.Expr.const `TrustIr.FuncId.index []) (Lean.Expr.bvar 2)))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `ToString.toString [Lean.Level.zero])
                                        (Lean.Expr.const `String []))
                                      (Lean.Expr.const `instToStringString []))
                                    (Lean.Expr.lit (Lean.Literal.strVal " body is unsupported: ")))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `ToString.toString [Lean.Level.zero])
                                    (Lean.Expr.const `String []))
                                  (Lean.Expr.const `instToStringString []))
                                (Lean.Expr.bvar 0)))))
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.lam
                      `message
                      (Lean.Expr.const `String [])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Option.some [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.SemError []))
                        (Lean.Expr.app
                          (Lean.Expr.const `TrustIr.SemError.typeError [])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `HAppend.hAppend
                                        [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `String []))
                                    (Lean.Expr.const `String []))
                                  (Lean.Expr.const `String []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `instHAppendOfAppend [Lean.Level.zero])
                                    (Lean.Expr.const `String []))
                                  (Lean.Expr.const `instAppendString [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `HAppend.hAppend
                                            [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `String []))
                                        (Lean.Expr.const `String []))
                                      (Lean.Expr.const `String []))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `instHAppendOfAppend [Lean.Level.zero])
                                        (Lean.Expr.const `String []))
                                      (Lean.Expr.const `instAppendString [])))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `HAppend.hAppend
                                                [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                              (Lean.Expr.const `String []))
                                            (Lean.Expr.const `String []))
                                          (Lean.Expr.const `String []))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `instHAppendOfAppend [Lean.Level.zero])
                                            (Lean.Expr.const `String []))
                                          (Lean.Expr.const `instAppendString [])))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `ToString.toString [Lean.Level.zero])
                                            (Lean.Expr.const `String []))
                                          (Lean.Expr.const `instToStringString []))
                                        (Lean.Expr.lit (Lean.Literal.strVal "function "))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `ToString.toString [Lean.Level.zero])
                                          (Lean.Expr.const `Nat []))
                                        (Lean.Expr.const `instToStringNat []))
                                      (Lean.Expr.app (Lean.Expr.const `TrustIr.FuncId.index []) (Lean.Expr.bvar 2)))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `ToString.toString [Lean.Level.zero])
                                      (Lean.Expr.const `String []))
                                    (Lean.Expr.const `instToStringString []))
                                  (Lean.Expr.lit (Lean.Literal.strVal " body is malformed: ")))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `ToString.toString [Lean.Level.zero])
                                  (Lean.Expr.const `String []))
                                (Lean.Expr.const `instToStringString []))
                              (Lean.Expr.bvar 0)))))
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.lam
                    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@»._internal 0) "TrustIr") "Proofs") "DecodedFunctionLookupProps") 1775725367) "_hygCtx") "_hyg") 128)
                    (Lean.Expr.app
                      (Lean.Expr.const `List [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.BlockId []))
                        (Lean.Expr.const `TrustIr.BasicBlock [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `TrustIrEval.FunctionLookup.findError_prepare.match_1
                                [Lean.Level.succ (Lean.Level.zero)])
                              (Lean.Expr.lam
                                (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 149)
                                (Lean.Expr.app
                                  (Lean.Expr.const `Option [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.FuncId []))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.EvalFunction []))))
                                (Lean.Expr.app
                                  (Lean.Expr.const `Option [Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.SemError []))
                                (Lean.BinderInfo.default)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `List.find? [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.FuncId []))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.EvalFunction []))))
                                (Lean.Expr.lam
                                  `row
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.FuncId []))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.EvalFunction [])))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `BEq.beq [Lean.Level.zero])
                                          (Lean.Expr.const `TrustIr.FuncId []))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `instBEqOfDecidableEq [Lean.Level.zero])
                                            (Lean.Expr.const `TrustIr.FuncId []))
                                          (Lean.Expr.const `TrustIr.instDecidableEqFuncId [])))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Prod.fst [Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `TrustIr.FuncId []))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                            (Lean.Expr.const `TrustIr.EvalFunction [])))
                                        (Lean.Expr.bvar 0)))
                                    (Lean.Expr.bvar 3))
                                  (Lean.BinderInfo.default)))
                              (Lean.Expr.bvar 3)))
                          (Lean.Expr.lam
                            (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 172)
                            (Lean.Expr.const `TrustIr.FuncId [])
                            (Lean.Expr.lam
                              `message
                              (Lean.Expr.const `String [])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Option.some [Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.SemError []))
                                (Lean.Expr.app (Lean.Expr.const `TrustIr.SemError.typeError []) (Lean.Expr.bvar 0)))
                              (Lean.BinderInfo.default))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.lam
                          (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 196)
                          (Lean.Expr.const `TrustIr.FuncId [])
                          (Lean.Expr.lam
                            `feature
                            (Lean.Expr.const `String [])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Option.some [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.SemError []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `TrustIr.SemError.unsupported [])
                                  (Lean.Expr.const `TrustIr.UnsupportedFeature.ssaTypeTable []))
                                (Lean.Expr.bvar 0)))
                            (Lean.BinderInfo.default))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.lam
                        (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedFunctionLookupProps 1775725367) "_hygCtx") "_hyg") 206)
                        (Lean.Expr.app
                          (Lean.Expr.const `Option [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction []))))
                        (Lean.Expr.app
                          (Lean.Expr.const `Option.none [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.SemError []))
                        (Lean.BinderInfo.default)))
                    (Lean.BinderInfo.default)))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam
              `_
              (Lean.Expr.const `Unit [])
              (Lean.Expr.app (Lean.Expr.const `Option.none [Lean.Level.zero]) (Lean.Expr.const `TrustIr.SemError []))
              (Lean.BinderInfo.default)))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
    let originalErrorMatcher := Lean.mkIdent `TrustIrEval.FunctionLookup.findError_prepare.match_1
    let originalBlocksMatcher := Lean.mkIdent `TrustIrEval.FunctionLookup.findError_prepare.match_2
    let originalSourceMatcher := Lean.mkIdent `TrustIrEval.FunctionLookup.findError_prepare.match_3
    let originalSourceBodyMatcher := Lean.mkIdent `TrustIrEval.FunctionLookup.findError_prepare.match_6
    let proofSyntax ← `(term| by
      intro source definitions id
      lookupPropsOriginalAddBlocksMatcher
      unfold findError
      rw [sourceStatuses_prepare, executables_prepare]
      generalize (source.find? (fun function => function.id == id)) = selected
      induction selected using $originalSourceMatcher:ident
      · rename_i function
        delta $originalSourceBodyMatcher:ident
        dsimp only []
        simp only [Option.map]
        generalize function.blocks = selectedBlocks
        induction selectedBlocks using $originalBlocksMatcher:ident
        · rename_i feature
          rfl
        · rename_i message
          rfl
        · rename_i rows
          simp only [Except.map]
          generalize (definitions.find? (fun row => row.fst == id)) = selectedDefinition
          induction selectedDefinition using $originalErrorMatcher:ident
          · rename_i key message
            rfl
          · rename_i key feature
            rfl
          · rename_i remaining
            cases remaining with
            | none => rfl
            | some row =>
              rcases row with ⟨key, result⟩
              cases result with
              | ok function => rfl
              | error error => cases error <;> rfl
      · rename_i unit
        cases unit
        rfl
    )
    lookupPropsAddExactOriginalTheorem `TrustIrEval.FunctionLookup.findError_prepare canonicalType proofSyntax
  else throwError "unsupported compiler for original canonical type preservation"

lookupPropsOriginalErrorCanonical
/-- EXACT original lazy error query. First raw decode status has priority;
    only an okay first raw row consults the first retained executable result.
    A missing raw row suppresses unrelated executable errors. -/
theorem findError_prepare (source : List Function)
    (definitions : List (FuncId × D EvalFunction)) (id : FuncId) :
    findError (prepare source definitions) id =
      match source.find? (fun function => function.id == id) with
      | some function => match function.blocks with
        | Except.error (.unsupported feature) => some (.unsupported .interproceduralCall
            s!"function {id.index} body is unsupported: {feature}")
        | Except.error (.malformed message) => some (.typeError
            s!"function {id.index} body is malformed: {message}")
        | Except.ok _ => match definitions.find? (fun row => row.fst == id) with
          | some (_, Except.error (.malformed message)) => some (.typeError message)
          | some (_, Except.error (.unsupported feature)) => some (.unsupported .ssaTypeTable feature)
          | _ => none
      | none => none := by
  trustIrCompilerProof {
  unfold findError
  rw [sourceStatuses_prepare, executables_prepare]
  cases source.find? (fun function => function.id == id) with
  | none => rfl
  | some function =>
    simp only [Option.map]
    cases body : function.blocks with
    | error error =>
      simp only [Except.map]
      cases error <;> rfl
    | ok rows =>
      simp only [Except.map]
      cases executable : definitions.find? (fun row => row.fst == id) with
      | none => rfl
      | some row =>
        rcases row with ⟨key, result⟩
        cases result with
        | ok function => rfl
        | error error => cases error <;> rfl
  } {
    unfold findError
    rw [sourceStatuses_prepare, executables_prepare]
    generalize (source.find? (fun function => function.id == id)) = selected
    induction selected using findError_prepare.match_3
    · rename_i function
      simp only [Option.map]
      cases body : function.blocks with
      | error error =>
        simp only [Except.map]
        cases error <;> rfl
      | ok rows =>
        simp only [Except.map]
        cases executable : definitions.find? (fun row => row.fst == id) with
        | none => rfl
        | some row =>
          rcases row with ⟨key, result⟩
          cases result with
          | ok function => rfl
          | error error => cases error <;> rfl
    · rename_i unit
      cases unit
      rfl
  }

end TrustIrEval.FunctionLookup

namespace TrustIrEval.FunctionLookup.SeedControls
open TrustIr

private def incoming (id : FuncId) : Function :=
  { id, name := "non-declaration", ty := ⟨0⟩, entry := ⟨0⟩,
    isDeclaration := false, blocks := Except.ok [] }

private def executable : EvalFunction :=
  { body := {paramTys := [], returnTys := []}, cfg := fun _ => none, entryBlock := ⟨0⟩ }

/-- Nonempty seed occupancy is genuine priority, not merely a property of
    preparation from empty. A later okay row cannot clear a stored error or
    erase a declaration bit. This raw-table control makes no validator claim. -/
theorem nonempty_error_seeds_and_declaration_survive :
    let id : FuncId := ⟨2^128 + 7⟩
    let statuses : NatIndex (D Unit) :=
      NatIndex.empty.insert id.index (Except.error (.unsupported "seed decode"))
    let declarations : NatIndex Unit := NatIndex.empty.insert id.index ()
    let definitions : NatIndex (D EvalFunction) :=
      NatIndex.empty.insert id.index (Except.error (.malformed "seed metadata"))
    (prepareSourceFrom [incoming id] statuses declarations).1.find? id.index =
        some (Except.error (.unsupported "seed decode")) ∧
      (prepareSourceFrom [incoming id] statuses declarations).2.contains id.index = true ∧
      (prepareDefsFrom [(id, Except.ok executable)] definitions).find? id.index =
        some (Except.error (.malformed "seed metadata")) := by
  dsimp only
  constructor
  · rw [prepareSourceFrom_statuses, NatIndex.find?_insert_same]
  · constructor
    · rw [prepareSourceFrom_declarations]
      simp only [NatIndex.contains, NatIndex.find?_insert_same, Option.isSome, Bool.true_or]
    · rw [prepareDefsFrom_find, NatIndex.find?_insert_same]

/-- Occupancy is independent of the payload: even a stored `none` is an
    occupied SOME and cannot be replaced. No scalar index implementation is
    unfolded; the exact proved insert/lookup laws discharge this sparse key. -/
theorem some_none_seed_is_occupied :
    let key := 2^128 + 7
    let index : NatIndex (Option Nat) := NatIndex.empty.insert key none
    (insertFirst index key (some 99)).find? key = some none := by
  dsimp only
  rw [insertFirst_find, NatIndex.find?_insert_same]

end TrustIrEval.FunctionLookup.SeedControls
