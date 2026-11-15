-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Eval

/-! Lookup laws for removing unreferenced, bodyless declaration rows.
These local facts do not claim whole-evaluator or code-generation equivalence.
The producer must still establish complete dependency and runtime preservation. -/

namespace TrustIr

theorem funcId_beq_eq_decide (a b : FuncId) : (a == b) = decide (a = b) := rfl

/-- Dropping declaration rows never reindexes a kept identity. -/
def projectDeclarationRows {α : Type} (removed : FuncId → Bool)
    (rows : List (FuncId × α)) : List (FuncId × α) :=
  rows.filter (fun row => !removed row.1)

/-- First physical lookup, including duplicate-key behavior, is preserved for
    every retained identity. No dense-ID or sorted-table premise is hidden. -/
theorem lookup_projectDeclarationRows {α : Type} (removed : FuncId → Bool)
    (id : FuncId) (retained : removed id = false) (rows : List (FuncId × α)) :
    (projectDeclarationRows removed rows).find? (fun row => decide (row.1 = id))
      = rows.find? (fun row => decide (row.1 = id)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    by_cases hit : row.1 = id
    · simp [projectDeclarationRows, List.find?, hit, retained]
    · cases hr : removed row.1 <;>
        simpa [projectDeclarationRows, List.find?, hit, hr] using ih

/-- The semantic definition table already omits bodyless rows. Removing only
    those rows preserves the complete table, not merely a selected entry. -/
theorem definitionRows_projectDeclarationRows (removed : FuncId → Bool)
    (rows : List (FuncId × Option EvalFunction))
    (bodyless : ∀ row ∈ rows, removed row.1 = true → row.2 = none) :
    (projectDeclarationRows removed rows).filterMap
        (fun row => row.2.map (fun body => (row.1, body)))
      = rows.filterMap (fun row => row.2.map (fun body => (row.1, body))) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have tail : ∀ r ∈ rest, removed r.1 = true → r.2 = none :=
      fun r h => bodyless r (List.mem_cons_of_mem row h)
    have tailEq := ih tail
    dsimp [projectDeclarationRows] at tailEq
    cases h : removed row.1
    · simp [projectDeclarationRows, List.filterMap, h, tailEq]
    · have absent := bodyless row (by simp) h
      simp [projectDeclarationRows, List.filterMap, h, absent, tailEq]


/-- Only declaration-status changes; all semantic tables and identities stay. -/
def withoutDeclarations (ctx : EvalContext) (removed : FuncId → Bool) : EvalContext :=
  { ctx with declared := fun id => if removed id then false else ctx.declared id }

theorem lookupDirectCallee_withoutDeclarations (ctx : EvalContext)
    (removed : FuncId → Bool) (id : FuncId) (retained : removed id = false)
    (declaredMessage missingMessage : String) :
    (withoutDeclarations ctx removed).lookupDirectCallee id declaredMessage missingMessage
      = ctx.lookupDirectCallee id declaredMessage missingMessage := by
  simp [EvalContext.lookupDirectCallee, withoutDeclarations, retained]

theorem resolveDrop_withoutDeclarations (ctx : EvalContext)
    (removed : FuncId → Bool) (inst : Inst) :
    (withoutDeclarations ctx removed).resolveDrop inst = ctx.resolveDrop inst := by
  cases inst <;> rfl

/-- Refusal control: erasing a CALLED declaration changes its named error.
    Hence the unused-reference premise is essential, not a proof shortcut. -/
theorem calledDeclaration_erasure_changes_refusal (ctx : EvalContext)
    (removed : FuncId → Bool) (id : FuncId) (absent : ctx.functions id = none)
    (declared : ctx.declared id = true) (erased : removed id = true)
    (state : MachineState) (declaredMessage missingMessage : String) :
    Sem.run (ctx.lookupDirectCallee id declaredMessage missingMessage) state
        = .error (.unsupported .interproceduralCall declaredMessage)
      ∧ Sem.run ((withoutDeclarations ctx removed).lookupDirectCallee
          id declaredMessage missingMessage) state = .error (.typeError missingMessage) := by
  simp [EvalContext.lookupDirectCallee, withoutDeclarations, absent, declared, erased,
    Sem.run, Sem.throwUnsupported, Sem.throwTypeError]
  constructor <;> rfl

end TrustIr
