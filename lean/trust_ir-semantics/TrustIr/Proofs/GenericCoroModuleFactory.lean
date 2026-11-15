-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.DecodedModule
import TrustIr.Proofs.GenericCoroAllBlocksFactory

namespace TrustIr.GenericCoro.ModuleFactory
open TrustIrEval GenericCoroAllBlocksPlanner GenericCoroFreshIds

/-- The actual rows and inference results from one execution of the existing
    all-block algorithm. Proofs connect this row-returning interface to the
    published evaluator-function interface; execution never calls both. -/
inductive RowExpansion (domain : Nat) (blocks : Rows) where
  | unchanged (source : LocalTypeInference)
  | capacity (source : LocalTypeInference) (certificate : AllBlocks.NoSchedule domain blocks)
  | expanded (rows : Rows) (source target : LocalTypeInference)

def RowExpansion.toFunctions {domain : Nat} {blocks : Rows}
    (header : EvalFunction) : RowExpansion domain blocks → AllBlocks.Expansion domain blocks
  | .unchanged source => .unchanged (AllBlocks.withInferredGraph header blocks source)
  | .capacity source certificate => .capacity (AllBlocks.withInferredGraph header blocks source) certificate
  | .expanded rows source target => .expanded (AllBlocks.withInferredGraph header blocks source)
      (AllBlocks.withInferredGraph header rows target)

/-- Source inference precedes allocation. A changed body has one cursor,
    one row traversal and one target-inference run. The literal emitted rows
    survive, rather than being reconstructed from a CFG closure. -/
def prepareRows (domain : Nat) (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (blocks : Rows) : Except SemError (RowExpansion domain blocks) := do
  let source ← inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks)
  if !(blocks.any (fun row => isSuspend row.2.terminator)) then
    return .unchanged source
  let planned := lowerRows domain blocks
  match outcome : planned.completion with
  | .capacity delta short covers full =>
    have certificate : AllBlocks.NoSchedule domain blocks := by
      have actual := lowerRows_capacity_excludes_schedule domain blocks
      have completion : (lowerRows domain blocks).completion =
          .capacity delta short covers full := outcome
      simp only [completion] at actual
      exact actual
    return .capacity source certificate
  | .ready =>
    let target ← inferLocalTypesWithEvidence direct indirect
      (graphParams planned.rows) (graphNodes planned.rows)
    return .expanded planned.rows source target

/-- This is the same per-function factory, with its actual rows retained.
    The equality is a proof; the executable module producer does not invoke
    the old factory in order to rediscover its output. -/
theorem prepareRows_toFunctions (domain : Nat) (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (header : EvalFunction) (blocks : Rows) :
    (prepareRows domain direct indirect blocks).map (RowExpansion.toFunctions header) =
      AllBlocks.functionsWithDomain domain direct indirect header blocks := by
  trustIrCompilerProof {
    cases source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
    | error error => simp only [prepareRows, AllBlocks.functionsWithDomain, source,
        Bind.bind, Except.bind, Except.map]
    | ok inferred =>
      cases changed : blocks.any (fun row => isSuspend row.2.terminator) with
      | false => simp only [prepareRows, AllBlocks.functionsWithDomain, source,
          Bind.bind, Except.bind, changed, Bool.not_false, if_true, Pure.pure,
          Except.pure, Except.map, RowExpansion.toFunctions]
      | true =>
        simp only [prepareRows, AllBlocks.functionsWithDomain, source,
          Bind.bind, Except.bind, changed, Bool.not_true, Bool.false_eq_true,
          if_false, Pure.pure, Except.pure]
        split
        · simp only [Except.map, RowExpansion.toFunctions]
          split <;> first | rfl | simp_all only [Completion.noConfusion]
        · cases target : inferLocalTypesWithEvidence direct indirect
            (graphParams (lowerRows domain blocks).rows) (graphNodes (lowerRows domain blocks).rows)
          all_goals simp only [target, Except.map, Bind.bind, Except.bind,
            Pure.pure, Except.pure, RowExpansion.toFunctions]
          all_goals split <;> first | rfl | simp_all only [Completion.noConfusion]
  } {
    have completion_capacity_not_ready {domain : Nat} {used : List Nat}
        (state : GenericCoroFreshCursor.Cursor domain used) (delta : List Nat) (short : delta.length < 3)
        (covers : ∀ key, key < domain → key ∈ state.reserved ++ used)
        (full : state.next = domain) :
        (Completion.capacity delta short covers full : Completion state) ≠ .ready := by
      intro impossible
      cases impossible
    cases source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
    | error error => simp only [prepareRows, AllBlocks.functionsWithDomain, source,
        Bind.bind, Except.bind, Except.map]
    | ok inferred =>
      cases changed : blocks.any (fun row => isSuspend row.2.terminator) with
      | false => simp only [prepareRows, AllBlocks.functionsWithDomain, source,
          Bind.bind, Except.bind, changed, Bool.not_false, if_true, Pure.pure,
          Except.pure, Except.map, RowExpansion.toFunctions]
      | true =>
        simp only [prepareRows, AllBlocks.functionsWithDomain, source,
          Bind.bind, Except.bind, changed, Bool.not_true, Bool.false_eq_true,
          if_false, Pure.pure, Except.pure]
        split
        · simp only [Except.map, RowExpansion.toFunctions]
          split <;> first | rfl | contradiction | simp_all only [completion_capacity_not_ready]
        · cases target : inferLocalTypesWithEvidence direct indirect
            (graphParams (lowerRows domain blocks).rows) (graphNodes (lowerRows domain blocks).rows)
          all_goals simp only [target, Except.map, Bind.bind, Except.bind,
            Pure.pure, Except.pure, RowExpansion.toFunctions]
          all_goals split <;> first | rfl | contradiction | simp_all only [completion_capacity_not_ready]
  }

def RowsReady (domain : Nat) (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (blocks : Rows) : RowExpansion domain blocks → Prop
  | .unchanged source =>
    inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) = .ok source ∧
      blocks.any (fun row => isSuspend row.2.terminator) = false
  | .capacity source _ =>
    inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) = .ok source
  | .expanded rows source target =>
    inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) = .ok source ∧
    rows = (lowerRows domain blocks).rows ∧ Ready (lowerRows domain blocks) ∧
    inferLocalTypesWithEvidence direct indirect (graphParams rows) (graphNodes rows) = .ok target ∧
    suspendCount rows = 0

theorem prepareRows_ready (domain : Nat) (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (blocks : Rows) (result : RowExpansion domain blocks)
    (actual : prepareRows domain direct indirect blocks = .ok result) :
    RowsReady domain direct indirect blocks result := by
  trustIrCompilerProof {
    cases source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
    | error error => simp only [prepareRows, source, Bind.bind, Except.bind] at actual
    | ok inferred =>
      cases changed : blocks.any (fun row => isSuspend row.2.terminator) with
      | false =>
        simp only [prepareRows, source, Bind.bind, Except.bind, changed, Bool.not_false,
          if_true, Pure.pure, Except.pure, Except.ok.injEq] at actual
        cases actual
        exact ⟨source, changed⟩
      | true =>
        simp only [prepareRows, source, Bind.bind, Except.bind, changed, Bool.not_true,
          Bool.false_eq_true, if_false, Pure.pure, Except.pure] at actual
        split at actual
        · cases actual
          exact source
        · rename_i completion
          cases target : inferLocalTypesWithEvidence direct indirect
              (graphParams (lowerRows domain blocks).rows) (graphNodes (lowerRows domain blocks).rows) with
          | error error => simp only [target, Bind.bind, Except.bind] at actual
          | ok targetInferred =>
            simp only [target, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at actual
            cases actual
            have ready : Ready (lowerRows domain blocks) := by simp only [Ready, completion]
            exact ⟨source, rfl, ready, target, (lowerRows_ready domain blocks ready).suspendCount_target_zero⟩
  } {
    cases source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
    | error error => simp only [prepareRows, source, Bind.bind, Except.bind] at actual <;> try contradiction
    | ok inferred =>
      cases changed : blocks.any (fun row => isSuspend row.2.terminator) with
      | false =>
        simp only [prepareRows, source, Bind.bind, Except.bind, changed, Bool.not_false,
          if_true, Pure.pure, Except.pure, Except.ok.injEq] at actual <;> try contradiction
        cases actual
        exact ⟨source, changed⟩
      | true =>
        simp only [prepareRows, source, Bind.bind, Except.bind, changed, Bool.not_true,
          Bool.false_eq_true, if_false, Pure.pure, Except.pure] at actual <;> try contradiction
        split at actual
        · cases actual
          exact source
        · rename_i completion
          cases target : inferLocalTypesWithEvidence direct indirect
              (graphParams (lowerRows domain blocks).rows) (graphNodes (lowerRows domain blocks).rows) with
          | error error => simp only [target, Bind.bind, Except.bind] at actual <;> try contradiction
          | ok targetInferred =>
            simp only [target, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at actual <;> try contradiction
            cases actual
            have ready : Ready (lowerRows domain blocks) := by simp only [Ready, completion]
            exact ⟨source, rfl, ready, target, (lowerRows_ready domain blocks ready).suspendCount_target_zero⟩
  }

/-- In the actual u32 domain, target inference cannot introduce a new
    refusal after successful source inference. This uses the published total
    factory property and the exact interface equality above. The auxiliary
    header is immaterial to lexical inference and is never executed. -/
theorem prepareRows_error_source (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (blocks : Rows) (error : SemError)
    (actual : prepareRows u32Domain direct indirect blocks = .error error) :
    inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) = .error error := by
  trustIrCompilerProof {
    cases source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
    | error sourceError =>
      simp only [prepareRows, source, Bind.bind, Except.bind, Except.error.injEq] at actual
      cases actual
      rfl
    | ok inferred =>
      let header : EvalFunction := { body := {paramTys := [], returnTys := []}, cfg := cfgOf blocks, entryBlock := ⟨0⟩ }
      obtain ⟨result, successful⟩ := AllBlocks.functions_defined direct indirect header blocks inferred source
      have same := prepareRows_toFunctions u32Domain direct indirect header blocks
      change AllBlocks.functionsWithDomain u32Domain direct indirect header blocks = .ok result at successful
      simp only [actual, Except.map, successful] at same
  } {
    cases source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
    | error sourceError =>
      simp only [prepareRows, source, Bind.bind, Except.bind, Except.error.injEq] at actual <;> try contradiction
      cases actual
      rfl
    | ok inferred =>
      let header : EvalFunction := { body := {paramTys := [], returnTys := []}, cfg := cfgOf blocks, entryBlock := ⟨0⟩ }
      obtain ⟨result, successful⟩ := AllBlocks.functions_defined direct indirect header blocks inferred source
      have same := prepareRows_toFunctions u32Domain direct indirect header blocks
      change AllBlocks.functionsWithDomain u32Domain direct indirect header blocks = .ok result at successful
      simp only [actual, Except.map, successful] at same <;> try contradiction
  }

/-- First source occurrence wins, including a retained missing signature.
    Source order and sparse identifiers are independent of the lookup index. -/
def headerIndex (signatures : Array FuncTyDef) (functions : List Function) :
    NatIndex (Option FuncTyDef) :=
  functions.foldr (fun function index =>
    index.insert function.id.index ((trustIrArrayGet? signatures function.ty.index))) NatIndex.empty

def firstHeader (signatures : Array FuncTyDef) : List Function → Nat → Option (Option FuncTyDef)
  | [], _ => none
  | function :: rest, key =>
    if key = function.id.index then some ((trustIrArrayGet? signatures function.ty.index))
    else firstHeader signatures rest key

theorem headerIndex_find (signatures : Array FuncTyDef) (functions : List Function) (key : Nat) :
    (headerIndex signatures functions).find? key = firstHeader signatures functions key := by
  induction functions with
  | nil => rfl
  | cons function rest ih =>
    simp only [headerIndex, List.foldr_cons, NatIndex.find?_insert, firstHeader]
    split <;> simp_all only [headerIndex]

def directHeaders (index : NatIndex (Option FuncTyDef)) (id : FuncId) : Option FuncTyDef :=
  (index.find? id.index).join

/-- Failures retain the original decoder error or inference error. Capacity
    carries the actual complete-schedule impossibility certificate. -/
inductive Problem where
  | decode (function : FuncId) (error : DecodeError)
  | inference (function : FuncId) (error : SemError)
  | capacity (function : FuncId) (blocks : Rows) (certificate : AllBlocks.NoSchedule u32Domain blocks)

def sameHeader (source target : Function) : Prop :=
  { target with blocks := source.blocks } = source

def noSuspendBody (function : Function) : Prop :=
  ∀ blocks, function.blocks = .ok blocks → suspendCount blocks = 0

def FunctionLaw (source target : Function) : Prop :=
  sameHeader source target ∧ (source.isDeclaration = true → target = source) ∧ noSuspendBody target

/-- Bodyless declarations stay bodyless. A manually forged declaration with
    nonempty rows is an explicit source error, not an executable definition.
    The real decoder already makes this distinction from the original rows. -/
def lowerFunction (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (function : Function) : Except Problem Function := do
  let blocks ← function.blocks.mapError (Problem.decode function.id)
  if function.isDeclaration then
    match blocks with
    | [] => return function
    | _ :: _ => throw (.decode function.id (.malformed s!"function {function.name}: declaration has a body"))
  else
    let _ ← match (trustIrArrayGet? signatures function.ty.index) with
      | some signature => .ok signature
      | none => .error (.decode function.id
          (.malformed s!"function {function.name}: func type {function.ty.index} not in table"))
    let prepared ← (prepareRows u32Domain direct (fun id => (trustIrArrayGet? signatures id.index)) blocks).mapError
      (Problem.inference function.id)
    match prepared with
    | .unchanged _ => return function
    | .capacity _ certificate => throw (.capacity function.id blocks certificate)
    | .expanded rows _ _ => return { function with blocks := .ok rows }

-- Reconstruct the original signature-case eliminator only on the modern pin.
run_cmd do
  if Lean.versionString == "4.8.0" then pure ()
  else if Lean.versionString == "4.30.0-rc2" then
    let originalName := Lean.mkIdent
      (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "lowerFunction") "match_2")
    Lean.Elab.Command.elabCommand (← `(command|
      def $originalName:ident.{u_1} (motive : Option FuncTyDef → Sort u_1)
          (signature : Option FuncTyDef)
          (h_1 : (signature : FuncTyDef) → motive (some signature))
          (h_2 : Unit → motive none) : motive signature :=
        Option.casesOn signature (h_2 ()) (fun signature => h_1 signature)))
  else throwError "unsupported compiler for original factory signature matcher"

theorem suspendCount_zero_of_any (blocks : Rows)
    (none : blocks.any (fun row => isSuspend row.2.terminator) = false) : suspendCount blocks = 0 := by
  trustIrCompilerProof {
    induction blocks with
    | nil => rfl
    | cons row rest ih =>
      cases head : isSuspend row.2.terminator with
      | true => simp only [List.any_cons, head, Bool.true_or] at none
      | false =>
        have tail : rest.any (fun row => isSuspend row.2.terminator) = false := by
          simpa only [List.any_cons, head, Bool.false_or] using none
        simp only [suspendCount, head, Bool.false_eq_true, if_false, Nat.zero_add, ih tail]
  } {
    induction blocks with
    | nil => rfl
    | cons row rest ih =>
      cases head : isSuspend row.2.terminator with
      | true => simp only [List.any_cons, head, Bool.true_or] at none <;> try contradiction
      | false =>
        have tail : rest.any (fun row => isSuspend row.2.terminator) = false := by
          simpa only [List.any_cons, head, Bool.false_or] using none
        simp only [suspendCount, head, Bool.false_eq_true, if_false, Nat.zero_add, ih tail]
  }

theorem lowerFunction_law (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (source target : Function) (actual : lowerFunction signatures direct source = .ok target) :
    FunctionLaw source target := by
  trustIrCompilerProof {
    cases body : source.blocks with
    | error error => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind] at actual
    | ok blocks =>
      cases declaration : source.isDeclaration with
      | true =>
        cases blocks with
        | nil =>
          simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
            if_true, Pure.pure, Except.pure, Except.ok.injEq] at actual
          cases actual
          refine ⟨rfl, fun _ => rfl, ?_⟩
          intro rows eq
          rw [body] at eq
          cases eq
          rfl
        | cons head tail =>
          simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
            if_true] at actual
      | false =>
        cases signature : signatures.get? source.ty.index with
        | none =>
          simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
            Bool.false_eq_true, if_false, signature] at actual
        | some signature =>
          cases prepared : prepareRows u32Domain direct (fun id => signatures.get? id.index) blocks with
          | error error =>
            simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
              Bool.false_eq_true, if_false, signature, prepared] at actual
          | ok expansion =>
            have valid := prepareRows_ready u32Domain direct (fun id => signatures.get? id.index)
              blocks expansion prepared
            cases expansion with
            | unchanged inferred =>
              simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                Bool.false_eq_true, if_false, signature, prepared, Pure.pure, Except.pure, Except.ok.injEq] at actual
              cases actual
              refine ⟨rfl, ?_, ?_⟩
              · intro impossible; rw [declaration] at impossible
              · intro rows eq
                rw [body] at eq
                cases eq
                exact suspendCount_zero_of_any blocks valid.2
            | capacity inferred certificate =>
              simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                Bool.false_eq_true, if_false, signature, prepared] at actual
            | expanded rows inferred targetInferred =>
              simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                Bool.false_eq_true, if_false, signature, prepared, Pure.pure, Except.pure, Except.ok.injEq] at actual
              cases actual
              refine ⟨?_, ?_, ?_⟩
              · cases source; cases declaration; rfl
              · intro impossible; rw [declaration] at impossible; contradiction
              · intro emitted eq
                cases eq
                exact valid.2.2.2.2
  } {
    cases body : source.blocks with
    | error error => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind] at actual <;> try contradiction
    | ok blocks =>
      cases declaration : source.isDeclaration with
      | true =>
        cases blocks with
        | nil =>
          simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
            if_true, Pure.pure, Except.pure, Except.ok.injEq] at actual <;> try contradiction
          cases actual
          refine ⟨rfl, fun _ => rfl, ?_⟩
          intro rows eq
          rw [body] at eq
          cases eq
          rfl
        | cons head tail =>
          simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
            if_true] at actual <;> try contradiction
      | false =>
        have finish : ∀ choice : Option FuncTyDef,
            (trustIrArrayGet? signatures source.ty.index) = choice → FunctionLaw source target := by
          intro choice
          refine lowerFunction.match_2
            (fun choice => (trustIrArrayGet? signatures source.ty.index) = choice →
              FunctionLaw source target) choice ?_ ?_
          · intro found signature
            cases prepared : prepareRows u32Domain direct (fun id => (trustIrArrayGet? signatures id.index)) blocks with
            | error error =>
              simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                Bool.false_eq_true, if_false, signature, prepared] at actual <;> try contradiction
            | ok expansion =>
              have valid := prepareRows_ready u32Domain direct (fun id => (trustIrArrayGet? signatures id.index))
                blocks expansion prepared
              cases expansion with
              | unchanged inferred =>
                simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                  Bool.false_eq_true, if_false, signature, prepared, Pure.pure, Except.pure, Except.ok.injEq] at actual <;> try contradiction
                cases actual
                refine ⟨rfl, ?_, ?_⟩
                · intro impossible; rw [declaration] at impossible
                · intro rows eq
                  rw [body] at eq
                  cases eq
                  exact suspendCount_zero_of_any blocks valid.2
              | capacity inferred certificate =>
                simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                  Bool.false_eq_true, if_false, signature, prepared] at actual <;> try contradiction
              | expanded rows inferred targetInferred =>
                simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                  Bool.false_eq_true, if_false, signature, prepared, Pure.pure, Except.pure, Except.ok.injEq] at actual <;> try contradiction
                cases actual
                refine ⟨?_, ?_, ?_⟩
                · cases source; cases declaration; rfl
                · intro impossible; rw [declaration] at impossible; contradiction
                · intro emitted eq
                  cases eq
                  exact valid.2.2.2.2
          · intro unit signature
            simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
              Bool.false_eq_true, if_false, signature] at actual <;> try contradiction
        exact finish (trustIrArrayGet? signatures source.ty.index) rfl
  }

inductive FunctionsLaw : List Function → List Function → Prop where
  | nil : FunctionsLaw [] []
  | cons {source target sources targets} : FunctionLaw source target → FunctionsLaw sources targets →
      FunctionsLaw (source :: sources) (target :: targets)

/-- Source-order, tail-recursive traversal with one final reversal. No
    partially transformed function list is exposed by an error outcome. -/
def lowerFunctionsLoop (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef) :
    List Function → List Function → Except Problem (List Function)
  | [], reversed => .ok reversed.reverse
  | function :: rest, reversed => do
    let target ← lowerFunction signatures direct function
    lowerFunctionsLoop signatures direct rest (target :: reversed)

inductive Outcome where
  | rejected (original : Module) (problem : Problem)
  | ready (target : Module)

/-- The sole publication point. Every original table and module field is
    retained by the record update; function order includes declarations. -/
def transform (source : Module) : Outcome :=
  let signatures := source.funcTys.toArray
  let headers := headerIndex signatures source.functions
  match lowerFunctionsLoop signatures (directHeaders headers) source.functions [] with
  | .error problem => .rejected source problem
  | .ok functions => .ready { source with functions }

theorem lowerFunctionsLoop_ready (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (source reversed target : List Function)
    (actual : lowerFunctionsLoop signatures direct source reversed = .ok target) :
    ∃ emitted, target = reversed.reverse ++ emitted ∧ FunctionsLaw source emitted := by
  trustIrCompilerProof {
    induction source generalizing reversed target with
    | nil =>
      cases actual
      exact ⟨[], (List.append_nil _).symm, .nil⟩
    | cons function rest ih =>
      cases result : lowerFunction signatures direct function with
      | error problem => simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual
      | ok lowered =>
        simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual
        obtain ⟨emitted, rows, relation⟩ := ih (lowered :: reversed) target actual
        refine ⟨lowered :: emitted, ?_, .cons (lowerFunction_law signatures direct function lowered result) relation⟩
        simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using rows
  } {
    induction source generalizing reversed target with
    | nil =>
      cases actual
      exact ⟨[], (List.append_nil _).symm, .nil⟩
    | cons function rest ih =>
      cases result : lowerFunction signatures direct function with
      | error problem => simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual <;> try contradiction
      | ok lowered =>
        simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual <;> try contradiction
        obtain ⟨emitted, rows, relation⟩ := ih (lowered :: reversed) target actual
        refine ⟨lowered :: emitted, ?_, .cons (lowerFunction_law signatures direct function lowered result) relation⟩
        simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using rows
  }

def FunctionHeader := FuncId × String × FuncTyId × BlockId × Bool × CallingConv

def functionHeader (function : Function) : FunctionHeader :=
  (function.id, function.name, function.ty, function.entry, function.isDeclaration, function.callingConvention)

theorem sameHeader_header {source target : Function} (same : sameHeader source target) :
    functionHeader target = functionHeader source := by
  have equality : { target with blocks := source.blocks } = source := same
  have projected := congrArg functionHeader equality
  exact projected

theorem FunctionsLaw.headers {source target : List Function} (relation : FunctionsLaw source target) :
    target.map functionHeader = source.map functionHeader := by
  induction relation with
  | nil => rfl
  | cons law _ ih =>
    simp only [List.map_cons, sameHeader_header law.1, ih]

theorem FunctionsLaw.noSuspends {source target : List Function} (relation : FunctionsLaw source target) :
    ∀ function ∈ target, noSuspendBody function := by
  induction relation with
  | nil => intro function member; cases member
  | cons law _ ih =>
    intro function member
    cases member with
    | head => exact law.2.2
    | tail _ member => exact ih function member

theorem FunctionsLaw.declarations {source target : List Function} (relation : FunctionsLaw source target) :
    ∀ function ∈ source, function.isDeclaration = true → function ∈ target := by
  induction relation with
  | nil => intro function member; cases member
  | @cons source target sources targets law _rest ih =>
    intro function member declaration
    cases member with
    | head => rw [law.2.1 declaration]; exact List.Mem.head _
    | tail _ member => exact List.Mem.tail _ (ih function member declaration)

/-- Every module field other than the function list is literally retained.
    The paired list law also fixes complete function headers and declarations. -/
theorem transform_ready (source target : Module) (actual : transform source = .ready target) :
    { target with functions := source.functions } = source ∧ FunctionsLaw source.functions target.functions := by
  unfold transform at actual
  dsimp only at actual
  split at actual
  · contradiction
  · rename_i functions complete
    cases actual
    obtain ⟨emitted, rows, relation⟩ := lowerFunctionsLoop_ready source.funcTys.toArray
      (directHeaders (headerIndex source.funcTys.toArray source.functions)) source.functions [] functions complete
    simp only [List.reverse_nil, List.nil_append] at rows
    cases source
    exact ⟨rfl, rows.symm ▸ relation⟩

theorem transform_headers (source target : Module) (actual : transform source = .ready target) :
    target.functions.map functionHeader = source.functions.map functionHeader :=
  (transform_ready source target actual).2.headers

theorem transform_noSuspends (source target : Module) (actual : transform source = .ready target) :
    ∀ function ∈ target.functions, ∀ blocks, function.blocks = .ok blocks → suspendCount blocks = 0 :=
  (transform_ready source target actual).2.noSuspends

theorem transform_declarations (source target : Module) (actual : transform source = .ready target) :
    ∀ function ∈ source.functions, function.isDeclaration = true → function ∈ target.functions :=
  (transform_ready source target actual).2.declarations

/-- Failure never publishes an already-processed prefix as a target module. -/
theorem transform_rejected_original (source original : Module) (problem : Problem)
    (actual : transform source = .rejected original problem) : original = source := by
  unfold transform at actual
  dsimp only at actual
  split at actual
  · cases actual; rfl
  · contradiction

theorem lowerFunction_decode_error (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (function : Function) (error : DecodeError) (body : function.blocks = .error error) :
    lowerFunction signatures direct function = .error (.decode function.id error) := by
  simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind]

theorem sameHeader_id {source target : Function} (same : sameHeader source target) : target.id = source.id := by
  have equality : { target with blocks := source.blocks } = source := same
  have projected := congrArg Function.id equality
  exact projected

theorem sameHeader_ty {source target : Function} (same : sameHeader source target) : target.ty = source.ty := by
  have equality : { target with blocks := source.blocks } = source := same
  have projected := congrArg Function.ty equality
  exact projected

theorem FunctionsLaw.headerIndex (signatures : Array FuncTyDef) {source target : List Function}
    (relation : FunctionsLaw source target) : headerIndex signatures target = headerIndex signatures source := by
  trustIrCompilerProof {
    induction relation with
    | nil => rfl
    | @cons source target sources targets law _rest ih =>
      change (ModuleFactory.headerIndex signatures targets).insert target.id.index (signatures.get? target.ty.index) =
        (ModuleFactory.headerIndex signatures sources).insert source.id.index (signatures.get? source.ty.index)
      rw [sameHeader_id law.1, sameHeader_ty law.1, ih]
  } {
    induction relation with
    | nil => rfl
    | @cons source target sources targets law _rest ih =>
      change (ModuleFactory.headerIndex signatures targets).insert target.id.index ((trustIrArrayGet? signatures target.ty.index)) =
        (ModuleFactory.headerIndex signatures sources).insert source.id.index ((trustIrArrayGet? signatures source.ty.index))
      rw [sameHeader_id law.1, sameHeader_ty law.1, ih]
  }

theorem transform_directHeaders (source target : Module) (actual : transform source = .ready target) :
    directHeaders (headerIndex source.funcTys.toArray target.functions) =
      directHeaders (headerIndex source.funcTys.toArray source.functions) := by
  rw [(transform_ready source target actual).2.headerIndex]

/-- A successful AST publication is backed by the actual row preparation,
    not by a caller-supplied or independently reconstructed target graph. -/
def PreparedAt (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (source target : Function) : Prop :=
  (source.isDeclaration = true ∧ target = source) ∨
  ∃ blocks expansion, source.isDeclaration = false ∧ source.blocks = .ok blocks ∧
    prepareRows u32Domain direct (fun id => (trustIrArrayGet? signatures id.index)) blocks = .ok expansion ∧
    match expansion with
    | .unchanged _ => target = source
    | .capacity _ _ => False
    | .expanded rows _ _ => target = { source with blocks := .ok rows }

theorem lowerFunction_prepared (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (source target : Function) (actual : lowerFunction signatures direct source = .ok target) :
    PreparedAt signatures direct source target := by
  trustIrCompilerProof {
    cases body : source.blocks with
    | error error => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind] at actual
    | ok blocks =>
      cases declaration : source.isDeclaration with
      | true => exact Or.inl ⟨declaration, (lowerFunction_law signatures direct source target actual).2.1 declaration⟩
      | false =>
        cases signature : signatures.get? source.ty.index with
        | none => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind,
            declaration, Bool.false_eq_true, if_false, signature] at actual
        | some signature =>
          cases prepared : prepareRows u32Domain direct (fun id => signatures.get? id.index) blocks with
          | error error => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind,
              declaration, Bool.false_eq_true, if_false, signature, prepared] at actual
          | ok expansion =>
            cases expansion with
            | unchanged inferred =>
              simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                Bool.false_eq_true, if_false, signature, prepared, Pure.pure, Except.pure, Except.ok.injEq] at actual
              exact Or.inr ⟨blocks, _, declaration, body, prepared, actual.symm⟩
            | capacity inferred certificate => simp only [lowerFunction, body, Except.mapError, Bind.bind,
                Except.bind, declaration, Bool.false_eq_true, if_false, signature, prepared] at actual
            | expanded rows inferred targetInferred =>
              simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                Bool.false_eq_true, if_false, signature, prepared, Pure.pure, Except.pure, Except.ok.injEq] at actual
              refine Or.inr ⟨blocks, _, declaration, body, prepared, ?_⟩
              rw [← actual]
              cases source; cases declaration; rfl
  } {
    cases body : source.blocks with
    | error error => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind] at actual <;> try contradiction
    | ok blocks =>
      cases declaration : source.isDeclaration with
      | true => exact Or.inl ⟨declaration, (lowerFunction_law signatures direct source target actual).2.1 declaration⟩
      | false =>
        cases signature : (trustIrArrayGet? signatures source.ty.index) with
        | none => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind,
            declaration, Bool.false_eq_true, if_false, signature] at actual <;> try contradiction
        | some signature =>
          cases prepared : prepareRows u32Domain direct (fun id => (trustIrArrayGet? signatures id.index)) blocks with
          | error error => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind,
              declaration, Bool.false_eq_true, if_false, signature, prepared] at actual <;> try contradiction
          | ok expansion =>
            cases expansion with
            | unchanged inferred =>
              simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                Bool.false_eq_true, if_false, signature, prepared, Pure.pure, Except.pure, Except.ok.injEq] at actual <;> try contradiction
              exact Or.inr ⟨blocks, _, declaration, body, prepared, actual.symm⟩
            | capacity inferred certificate => simp only [lowerFunction, body, Except.mapError, Bind.bind,
                Except.bind, declaration, Bool.false_eq_true, if_false, signature, prepared] at actual <;> try contradiction
            | expanded rows inferred targetInferred =>
              simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind, declaration,
                Bool.false_eq_true, if_false, signature, prepared, Pure.pure, Except.pure, Except.ok.injEq] at actual <;> try contradiction
              refine Or.inr ⟨blocks, _, declaration, body, prepared, ?_⟩
              rw [← actual]
              cases source; cases declaration; rfl
  }

inductive Produced (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef) :
    List Function → List Function → Prop where
  | nil : Produced signatures direct [] []
  | cons {source target sources targets} (actual : lowerFunction signatures direct source = .ok target)
      (rest : Produced signatures direct sources targets) :
      Produced signatures direct (source :: sources) (target :: targets)

theorem lowerFunctionsLoop_produced (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (source reversed target : List Function)
    (actual : lowerFunctionsLoop signatures direct source reversed = .ok target) :
    ∃ emitted, target = reversed.reverse ++ emitted ∧ Produced signatures direct source emitted := by
  trustIrCompilerProof {
    induction source generalizing reversed target with
    | nil => cases actual; exact ⟨[], (List.append_nil _).symm, .nil⟩
    | cons function rest ih =>
      cases result : lowerFunction signatures direct function with
      | error problem => simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual
      | ok lowered =>
        simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual
        obtain ⟨emitted, rows, relation⟩ := ih (lowered :: reversed) target actual
        refine ⟨lowered :: emitted, ?_, .cons result relation⟩
        simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using rows
  } {
    induction source generalizing reversed target with
    | nil => cases actual; exact ⟨[], (List.append_nil _).symm, .nil⟩
    | cons function rest ih =>
      cases result : lowerFunction signatures direct function with
      | error problem => simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual <;> try contradiction
      | ok lowered =>
        simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual <;> try contradiction
        obtain ⟨emitted, rows, relation⟩ := ih (lowered :: reversed) target actual
        refine ⟨lowered :: emitted, ?_, .cons result relation⟩
        simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using rows
  }

theorem transform_produced (source target : Module) (actual : transform source = .ready target) :
    Produced source.funcTys.toArray (directHeaders (headerIndex source.funcTys.toArray source.functions))
      source.functions target.functions := by
  unfold transform at actual
  dsimp only at actual
  split at actual
  · contradiction
  · rename_i functions complete
    cases actual
    obtain ⟨emitted, rows, relation⟩ := lowerFunctionsLoop_produced source.funcTys.toArray
      (directHeaders (headerIndex source.funcTys.toArray source.functions)) source.functions [] functions complete
    simp only [List.reverse_nil, List.nil_append] at rows
    exact rows.symm ▸ relation

theorem lowerFunctionsLoop_error (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (source reversed : List Function) (problem : Problem)
    (actual : lowerFunctionsLoop signatures direct source reversed = .error problem) :
    ∃ function ∈ source, lowerFunction signatures direct function = .error problem := by
  trustIrCompilerProof {
    induction source generalizing reversed with
    | nil => simp only [lowerFunctionsLoop] at actual
    | cons function rest ih =>
      cases result : lowerFunction signatures direct function with
      | error error =>
        simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind, Except.error.injEq] at actual
        exact ⟨function, List.Mem.head _, actual ▸ result⟩
      | ok lowered =>
        simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual
        obtain ⟨failed, member, failure⟩ := ih (lowered :: reversed) actual
        exact ⟨failed, List.Mem.tail _ member, failure⟩
  } {
    induction source generalizing reversed with
    | nil => simp only [lowerFunctionsLoop] at actual <;> try contradiction
    | cons function rest ih =>
      cases result : lowerFunction signatures direct function with
      | error error =>
        simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind, Except.error.injEq] at actual <;> try contradiction
        exact ⟨function, List.Mem.head _, actual ▸ result⟩
      | ok lowered =>
        simp only [lowerFunctionsLoop, result, Bind.bind, Except.bind] at actual <;> try contradiction
        obtain ⟨failed, member, failure⟩ := ih (lowered :: reversed) actual
        exact ⟨failed, List.Mem.tail _ member, failure⟩
  }

theorem transform_rejected_at (source original : Module) (problem : Problem)
    (actual : transform source = .rejected original problem) :
    original = source ∧ ∃ function ∈ source.functions,
      lowerFunction source.funcTys.toArray
        (directHeaders (headerIndex source.funcTys.toArray source.functions)) function = .error problem := by
  have originalEq := transform_rejected_original source original problem actual
  refine ⟨originalEq, ?_⟩
  unfold transform at actual
  dsimp only at actual
  split at actual
  · rename_i failure complete
    cases actual
    exact lowerFunctionsLoop_error _ _ _ [] _ complete
  · contradiction

theorem Produced.prepared (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    {source target : List Function} (produced : Produced signatures direct source target) :
    ∀ index sourceFunction targetFunction,
      (trustIrListGet? source index) = some sourceFunction → (trustIrListGet? target index) = some targetFunction →
      PreparedAt signatures direct sourceFunction targetFunction := by
  induction produced with
  | nil => intro index sourceFunction targetFunction sourceAt; cases index <;> cases sourceAt
  | @cons source target sources targets actual _rest ih =>
    intro index sourceFunction targetFunction sourceAt targetAt
    cases index with
    | zero =>
      cases sourceAt
      cases targetAt
      exact lowerFunction_prepared signatures direct source target actual
    | succ index => exact ih index sourceFunction targetFunction sourceAt targetAt

end TrustIr.GenericCoro.ModuleFactory

#trustIrAxiomsExact TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_2 == []
