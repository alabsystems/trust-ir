-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixBody
import TrustIr.Proofs.GenericCoroPrefixGraph
import TrustIr.Proofs.GenericCoroPrefixTransfer
import TrustIr.Proofs.GenericCoroTermContext

namespace TrustIr.GenericCoro.Prefix

private theorem types_refl (ids : List ValueId) (types : Option LocalTypeTable) :
    TypesAgreeOn ids types types := by
  cases types with
  | none => exact .absent
  | some table => exact .present table table (fun _ _ => rfl)

theorem evalBody_congrOn (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (depth : Nat)
    (strat : PanicStrategy) (rows : List (Inst × List ValueId))
    (types : ∀ row ∈ rows, TypesAgreeOn (row.2 ++ operandIds row.1) sourceTypes targetTypes) :
    evalBody sourceRecurse (scopedContext base source sourceTypes) depth strat rows =
      evalBody targetRecurse (scopedContext base target targetTypes) depth strat rows := by
  apply evalBody_congr
  intro row member
  exact evalBodyStep_congr sourceRecurse targetRecurse base source target headers effects
    sourceTypes targetTypes depth strat row.1 row.2 (types row member)

/-- All source block effects are equal when active declarations are equal.
    Recursive callees may carry their own distinct inferred declarations. -/
theorem evalLayer_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (types : Option LocalTypeTable) (depth : Nat) (cfg : CFG) (pc : BlockId)
    (args : List Value) (strat : PanicStrategy)
    (transfers : ∀ block result,
      evalTransfer sourceRecurse (scopedContext base source types) depth cfg block strat result =
        evalTransfer targetRecurse (scopedContext base target types) depth cfg block strat result) :
    evalLayer sourceRecurse (scopedContext base source types) depth cfg pc args strat =
      evalLayer targetRecurse (scopedContext base target types) depth cfg pc args strat := by
  have body : ∀ rows,
      evalBody sourceRecurse (scopedContext base source types) depth strat rows =
        evalBody targetRecurse (scopedContext base target types) depth strat rows := by
    intro rows
    exact evalBody_congrOn sourceRecurse targetRecurse base source target headers effects types types depth strat rows
      (fun row _ => types_refl _ types)
  have term : ∀ inst,
      stepTermWithContext (scopedContext base source types) depth cfg inst strat =
        stepTermWithContext (scopedContext base target types) depth cfg inst strat := by
    intro inst
    exact GenericCoro.stepTermWithContext_congr _ _ depth cfg inst strat rfl
      (functionCallWithConvention_congr base source target headers types types)
      (closureCall_congr base source target headers types types)
      (fun operand _ value =>
        checkFunctionItemCalleeType_scoped_congr base source target types types operand value rfl)
      (fun _ _ _ => rfl)
      (resolveFunctionItemBody_congr base source target headers types types)
  have itemChecks (declared : List Ty) (values : List Value) :
      checkFunctionItemValues (scopedContext base source types) declared values =
        checkFunctionItemValues (scopedContext base target types) declared values :=
    GenericCoro.itemValues_constantContext (scopedContext base source types)
      (scopedContext base target types) rfl declared values
  rw [evalLayer_eq_transfer, evalLayer_eq_transfer]
  simp only [resolveBlock_scoped, itemChecks, body, term, transfers]

end TrustIr.GenericCoro.Prefix
