-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixLayer
import TrustIr.Proofs.GenericCoroProps

namespace TrustIr.GenericCoro.Prefix

/-- A body node continues the enclosing loop whenever it succeeds. Errors,
    including unwind states and every callback failure, remain unconstrained. -/
def OnlyYield (action : Sem (ForInStep Unit)) : Prop :=
  ∀ state result, Sem.run action state = .ok result → result.fst = .yield ()

theorem onlyYield_pure : OnlyYield (pure (.yield ()) : Sem (ForInStep Unit)) := by
  intro state result run
  exact congrArg Prod.fst (Except.ok.inj run.symm)

theorem onlyYield_throw (error : SemError) :
    OnlyYield (throw error : Sem (ForInStep Unit)) := by
  intro state result run
  cases run

theorem onlyYield_typeError (message : String) :
    OnlyYield (Sem.throwTypeError message : Sem (ForInStep Unit)) := onlyYield_throw _

theorem onlyYield_bind {α : Type} (first : Sem α) (next : α → Sem (ForInStep Unit))
    (continues : ∀ value, OnlyYield (next value)) : OnlyYield (first >>= next) := by
  intro state result run
  simp only [Sem.run_bind] at run
  cases firstRun : Sem.run first state with
  | error error => simp only [firstRun, Except.bind] at run <;> cases run
  | ok pair =>
    simp only [firstRun, Except.bind] at run
    exact continues pair.fst pair.snd result run

private theorem onlyYield_instCases (inst : Inst)
    {onCall : FuncId → List ValueId → Sem (ForInStep Unit)}
    {onIndirect : ValueId → FuncTyId → List ValueId → CallingConv → Sem (ForInStep Unit)}
    {onAssert onOther : Sem (ForInStep Unit)}
    {onPad : Bool → List Nat → Sem (ForInStep Unit)}
    (calls : ∀ id args, OnlyYield (onCall id args))
    (indirect : ∀ id sig args conv, OnlyYield (onIndirect id sig args conv))
    (assertion : OnlyYield onAssert)
    (pad : ∀ cleanup clauses, OnlyYield (onPad cleanup clauses))
    (other : OnlyYield onOther) :
    OnlyYield (match inst with
      | .Call id args => onCall id args
      | .CallIndirect id sig args conv => onIndirect id sig args conv
      | .Assert _ _ _ => onAssert
      | .LandingPad cleanup clauses => onPad cleanup clauses
      | _ => onOther) := by
  cases inst <;> first
    | exact calls _ _
    | exact indirect _ _ _ _
    | exact assertion
    | exact pad _ _
    | exact other

theorem evalBodyStep_onlyYield (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId) :
    OnlyYield (evalBodyStep recurse ctx depth strat (inst, dests)) := by
  unfold evalBodyStep
  dsimp only
  refine onlyYield_instCases inst ?_ ?_ ?_ ?_ ?_
  all_goals repeat' (first
    | with_reducible intro value
    | exact onlyYield_pure
    | exact onlyYield_throw _
    | exact onlyYield_typeError _
    | with_reducible refine onlyYield_bind _ _ ?_
      intro value
    | dsimp only
    | split)

/-- A successful body node cannot select the early-exit branch of `forIn`.
    This equality retains its complete state and every error outcome. -/
theorem onlyYield_bind_eq {α : Type} (action : Sem (ForInStep Unit))
    (continues : OnlyYield action) (next : ForInStep Unit → Sem α) :
    (action >>= next) = (action >>= fun _ => next (.yield ())) := by
  funext state
  change Sem.run (action >>= next) state =
    Sem.run (action >>= fun _ => next (.yield ())) state
  simp only [Sem.run_bind]
  cases run : Sem.run action state with
  | error error => rfl
  | ok pair =>
    have yields := continues state pair run
    simp only [Except.bind, yields]

theorem evalBody_nil (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) : evalBody recurse ctx depth strat [] = pure () := rfl

theorem evalBody_cons (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (row : Inst × List ValueId)
    (rest : List (Inst × List ValueId)) :
    evalBody recurse ctx depth strat (row :: rest) = (do
      let _ ← evalBodyStep recurse ctx depth strat row
      evalBody recurse ctx depth strat rest) := by
  simp only [evalBody, List.forIn_cons]
  rw [onlyYield_bind_eq _ (evalBodyStep_onlyYield recurse ctx depth strat row.fst row.snd)]

theorem evalBody_append (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (first rest : List (Inst × List ValueId)) :
    evalBody recurse ctx depth strat (first ++ rest) = (do
      evalBody recurse ctx depth strat first
      evalBody recurse ctx depth strat rest) := by
  induction first with
  | nil => simp only [List.nil_append, evalBody_nil, pure_bind]
  | cons row rows ih =>
    simp only [List.cons_append, evalBody_cons, ih, bind_assoc]

theorem forIn_sem_congr {α β : Type} (items : List α) (initial : β)
    (source target : α → β → Sem (ForInStep β))
    (same : ∀ item ∈ items, ∀ state, source item state = target item state) :
    forIn items initial source = forIn items initial target := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, List.forIn_cons, same item ((trustIrListMemConsSelf _ _)) initial]
    apply congrArg (fun next => target item initial >>= next)
    funext step
    cases step with
    | done value => rfl
    | yield value => exact ih value (fun item member => same item (List.mem_cons_of_mem _ member))

theorem evalBody_congr (sourceRecurse targetRecurse : Recurse)
    (sourceCtx targetCtx : EvalContext) (depth : Nat) (strat : PanicStrategy)
    (rows : List (Inst × List ValueId))
    (same : ∀ row ∈ rows,
      evalBodyStep sourceRecurse sourceCtx depth strat row =
        evalBodyStep targetRecurse targetCtx depth strat row) :
    evalBody sourceRecurse sourceCtx depth strat rows =
      evalBody targetRecurse targetCtx depth strat rows := by
  exact forIn_sem_congr rows ()
    (fun row _ => evalBodyStep sourceRecurse sourceCtx depth strat row)
    (fun row _ => evalBodyStep targetRecurse targetCtx depth strat row)
    (fun row member _ => same row member)



end TrustIr.GenericCoro.Prefix
