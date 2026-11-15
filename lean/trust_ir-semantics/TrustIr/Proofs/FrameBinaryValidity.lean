-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameUnaryValidity
import TrustIr.Proofs.FloatChoiceProps

namespace TrustIr.FrameLifetime

private theorem run_bind {α β : Type} (action : Sem α) (next : α → Sem β) (state : MachineState) :
    Sem.run (action >>= next) state =
      (Sem.run action state >>= fun pair => Sem.run (next pair.1) pair.2) := rfl

private theorem split_bind_success {α β : Type} (action : Sem α) (next : α → Sem β)
    (s final : MachineState) (result : β)
    (run : Sem.run (action >>= next) s = .ok (result, final)) :
    ∃ value middle, Sem.run action s = .ok (value, middle) ∧
      Sem.run (next value) middle = .ok (result, final) := by
  rw [run_bind] at run
  cases step : Sem.run action s with
  | error error => simp [step, bind, Except.bind] at run
  | ok pair => exact ⟨pair.1, pair.2, rfl, by simpa [step] using run⟩

private theorem except_success {α β : Type} (action : Except SemError α)
    (next : α → Except SemError β) (result : β)
    (run : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases step : action with
  | error error => simp [step, bind, Except.bind] at run
  | ok value => exact ⟨value, rfl, by simpa [step] using run⟩

private theorem except_map_minted {α : Type} (bound : Nat) (action : Except SemError α)
    (encode : α → Value) (result : Value) (known : ∀ value, MintedValue bound (encode value))
    (run : (do let value ← action; pure (encode value)) = .ok result) : MintedValue bound result := by
  cases computed : action with
  | error error => simp [computed, bind, Except.bind] at run
  | ok value =>
    simp [computed, bind, pure, Except.bind, Except.pure] at run
    cases run
    exact known value

/-- Typed Bool computation produces only a frame-free Bool result. -/
theorem bool_binary_minted (bound : Nat) (op : BinOp) (left right result : Value)
    (run : semBoolBinOpValues op left right = .ok result) : MintedValue bound result := by
  unfold semBoolBinOpValues at run
  split at run
  · simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, if_false,
      pure, Except.pure, bind, Except.bind] at run
    exact except_map_minted bound _ .bool result (mintedValue_bool bound) run
  · split at run <;> simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure, bind, Except.bind] at run

/-- Every successful vector binary lane computation produces a scalar leaf. -/
theorem binary_lane_minted (bound : Nat) (op : BinOp) (ty : Ty) (left right result : Value)
    (run : semVectorBinOpLane op ty left right = .ok result) : MintedValue bound result := by
  obtain ⟨unit, _, tail1⟩ := except_success (checkVectorLaneType ty false left) _ result run
  cases unit
  obtain ⟨unit, _, tail2⟩ := except_success (checkVectorLaneType ty false right) _ result tail1
  cases unit
  split at tail2
  · exact except_map_minted bound _ .bool result (mintedValue_bool bound) tail2
  · split at tail2
    · simp [throw, throwThe, MonadExceptOf.throw] at tail2
    · simp [throw, throwThe, MonadExceptOf.throw] at tail2
    · simp [throw, throwThe, MonadExceptOf.throw] at tail2
    · exact except_map_minted bound _ (.int _) result (mintedValue_int bound _) tail2
  · exact except_map_minted bound _ .float result (mintedValue_float bound) tail2
  · simp [throw, throwThe, MonadExceptOf.throw] at tail2

theorem binary_lanes_minted (bound : Nat) (op : BinOp) (ty : Ty) (left right output : List Value)
    (run : semVectorBinOp op ty left right = .ok output) :
    ∀ value ∈ output, MintedValue bound value := by
  induction left generalizing right output with
  | nil =>
    cases right <;> simp [semVectorBinOp] at run
    cases run
    intro value member
    cases member
  | cons first left ih =>
    cases right with
    | nil => simp [semVectorBinOp] at run
    | cons second right =>
      obtain ⟨value, computed, tail1⟩ := except_success (semVectorBinOpLane op ty first second) _ output run
      obtain ⟨remaining, computedRest, tail2⟩ := except_success (semVectorBinOp op ty left right) _ output tail1
      change Except.ok (value :: remaining) = Except.ok output at tail2
      cases tail2
      intro child member
      cases member with
      | head => exact binary_lane_minted bound op ty first second value computed
      | tail _ member => exact ih right remaining computedRest child member

private theorem vector_binary_minted (bound count : Nat) (op : BinOp) (ty : Ty)
    (left right : List Value) (result : Value)
    (run : (do
      checkVectorShape count ty left
      checkVectorShape count ty right
      pure (Value.vector (← semVectorBinOp op ty left right))) = .ok result) : MintedValue bound result := by
  obtain ⟨unit, _, tail1⟩ := except_success (checkVectorShape count ty left) _ result run
  cases unit
  obtain ⟨unit, _, tail2⟩ := except_success (checkVectorShape count ty right) _ result tail1
  cases unit
  obtain ⟨output, computed, tail3⟩ := except_success (semVectorBinOp op ty left right) _ result tail2
  change Except.ok (.vector output) = Except.ok result at tail3
  cases tail3
  exact (mintedValue_iff_shape bound (.vector output)).2 (binary_lanes_minted bound op ty left right output computed)

/-- Deterministic scalar/vector binary computation cannot create a frame
identity, independently of the operation's numeric result or input validity. -/
theorem binary_value_minted (bound : Nat) (op : BinOp) (ty : Ty) (left right result : Value)
    (run : semBinOpValues op ty left right = .ok result) : MintedValue bound result := by
  unfold semBinOpValues at run
  split at run
  · exact except_map_minted bound _ .bool result (mintedValue_bool bound) run
  · exact vector_binary_minted bound _ op _ _ _ result run
  · split at run
    · simp [throw, throwThe, MonadExceptOf.throw] at run
    · exact except_map_minted bound _ (.int _) result (mintedValue_int bound _) run
  · exact except_map_minted bound _ .float result (mintedValue_float bound) run
  · simp [throw, throwThe, MonadExceptOf.throw] at run

/-- Choice erasure changes only ghost execution input/cursor, so equality of
erased states suffices for the recursive frame identity invariant. -/
theorem WellMintedState.of_choice_erasure (before after : MachineState)
    (valid : WellMintedState before)
    (same : after.eraseFloatZeroChoices = before.eraseFloatZeroChoices) : WellMintedState after := by
  have locals := congrArg MachineState.locals same
  change after.locals = before.locals at locals
  have table := congrArg MachineState.openFrameLineages same
  change after.openFrameLineages = before.openFrameLineages at table
  have counter := congrArg MachineState.nextFrameLineage same
  change after.nextFrameLineage = before.nextFrameLineage at counter
  constructor
  · intro lineage member
    rw [table] at member
    rw [counter]
    exact valid.table lineage member
  · change MintedValues after.nextFrameLineage after.locals
    rw [counter, locals]
    exact valid.values

private def Safe {α : Type} (post : α → Prop) (action : Sem α) : Prop :=
  ∀ before after value, WellMintedState before → Sem.run action before = .ok (value, after) →
    WellMintedState after ∧ post value

private theorem safe_pure {α : Type} (post : α → Prop) (value : α) (known : post value) :
    Safe post (pure value) := by
  intro before after result valid run
  change Except.ok (value, before) = Except.ok (result, after) at run
  cases run
  exact ⟨valid, known⟩

private theorem safe_throw {α : Type} (post : α → Prop) (error : SemError) :
    Safe post (throw error : Sem α) := by
  intro before after value _ run
  cases run

private theorem safe_bind {α β : Type} (post : α → Prop) (target : β → Prop)
    (action : Sem α) (next : α → Sem β) (first : Safe post action)
    (rest : ∀ value, post value → Safe target (next value)) : Safe target (action >>= next) := by
  intro before after result valid run
  obtain ⟨value, middle, executed, tail⟩ := split_bind_success _ _ before after result run
  obtain ⟨middleValid, known⟩ := first before middle value valid executed
  exact rest value known middle after result middleValid tail

private theorem safe_lookup (id : ValueId) : Safe (fun _ => True) (Sem.lookupValue id) := by
  intro before after value valid run
  cases lookup : before.lookupValue id with
  | none =>
    simp [Sem.lookupValue, lookup, Sem.getState, Sem.throwTypeError, Sem.run,
      StateT.run, StateT.bind, StateT.get, StateT.lift, StateT.pure, bind, pure,
      Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  | some held =>
    simp [Sem.lookupValue, lookup, Sem.getState, Sem.run,
      StateT.run, StateT.bind, StateT.get, StateT.pure, bind, pure, Except.bind, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨valid, True.intro⟩

private theorem safe_reject (value : Value) (op : String) :
    Safe (fun _ => True) (Sem.rejectPartial value op) := by
  intro before after unit valid run
  cases unit
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> cases run <;> exact ⟨valid, True.intro⟩

private theorem safe_fresh (value : Value) (free : MintedValue 0 value) :
    Safe (fun _ => True) (Sem.bindFresh value) := by
  intro before after id valid run
  exact ⟨WellMintedState.fresh_success before after value id valid (free.mono (Nat.zero_le _)) run, True.intro⟩

private theorem safe_guard {α : Type} (post : α → Prop) (condition : Bool) (error : SemError)
    (action : Sem α) (safe : Safe post action) :
    Safe post (if condition then do
      let _ ← (throw error : Sem Unit)
      action
    else do
      let _ ← (pure () : Sem Unit)
      action) := by
  cases condition with
  | false => exact safe
  | true => intro before after value _ run; cases run

private theorem safe_minmax_at (op : BinOp) (ty : Ty) (left right : Float) :
    Safe (fun _ => True) (semFloatMinMaxAt op ty left right) := by
  intro before after value valid run
  obtain ⟨_, _, _, same⟩ := semFloatMinMaxAt_permitted run
  exact ⟨WellMintedState.of_choice_erasure before after valid same, True.intro⟩

private theorem safe_minmax_scalar (op : BinOp) (ty : Ty) (left right : Value) :
    Safe (MintedValue 0) (semFloatMinMaxScalarValue op ty left right) := by
  unfold semFloatMinMaxScalarValue
  refine safe_bind _ _ _ _ (safe_reject left "BinOp") ?_
  intro _ _
  refine safe_bind _ _ _ _ (safe_reject right "BinOp") ?_
  intro _ _
  refine safe_guard _ (!ty.isFloat) (.typeError "min/max requires a float type") _ ?_
  cases left <;> try { exact safe_throw _ _ }
  case float left =>
    cases right <;> try { exact safe_throw _ _ }
    case float right =>
      exact safe_bind _ _ _ _ (safe_minmax_at op ty left right)
        (fun value _ => safe_pure _ (Value.float value) (mintedValue_float 0 value))

private theorem safe_minmax_lanes (op : BinOp) (ty : Ty) (left right : List Value) :
    Safe (fun values => ∀ value ∈ values, MintedValue 0 value) (semFloatMinMaxLanes op ty left right) := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact safe_pure _ [] (fun _ member => nomatch member)
    | cons _ _ => exact safe_throw _ _
  | cons first left ih =>
    cases right with
    | nil => exact safe_throw _ _
    | cons second right =>
      refine safe_bind _ _ _ _ (safe_minmax_scalar op ty first second) ?_
      intro value free
      refine safe_bind _ _ _ _ (ih right) ?_
      intro values freeValues
      apply safe_pure _ (value :: values)
      intro child member
      cases member with
      | head => exact free
      | tail _ member => exact freeValues child member

private theorem safe_minmax_values (op : BinOp) (ty : Ty) (left right : Value) :
    Safe (MintedValue 0) (semFloatMinMaxValues op ty left right) := by
  unfold semFloatMinMaxValues
  refine safe_bind _ _ _ _ (safe_reject left "BinOp") ?_
  intro _ _
  refine safe_bind _ _ _ _ (safe_reject right "BinOp") ?_
  intro _ _
  cases ty <;> try { exact safe_minmax_scalar op _ left right }
  case Vector count elemTy =>
    refine safe_guard _ (count == 0) (.unsupported .vectorShape "zero-lane min/max vector") _ ?_
    refine safe_guard _ (!elemTy.isFloat) (.typeError "min/max requires float vector lanes") _ ?_
    cases left <;> try { exact safe_throw _ _ }
    case vector left =>
      cases right <;> try { exact safe_throw _ _ }
      case vector right =>
        refine safe_guard _ (left.length != count || right.length != count)
          (.typeError "min/max vector lane count does not match type") _ ?_
        exact safe_bind _ _ _ _ (safe_minmax_lanes op elemTy left right)
          (fun values free => safe_pure _ (Value.vector values) ((mintedValue_iff_shape 0 (.vector values)).2 free))

private theorem safe_binary_deterministic (op : BinOp) (ty : Ty) (left right : ValueId) :
    Safe (fun _ => True) (semBinOpDeterministic op ty left right) := by
  unfold semBinOpDeterministic
  refine safe_bind _ _ _ _ (safe_lookup left) ?_
  intro lhs _
  refine safe_bind _ _ _ _ (safe_lookup right) ?_
  intro rhs _
  refine safe_bind _ _ _ _ (safe_reject lhs "BinOp") ?_
  intro _ _
  refine safe_bind _ _ _ _ (safe_reject rhs "BinOp") ?_
  intro _ _
  cases computed : semBinOpValues op ty lhs rhs with
  | error error => exact safe_throw _ error
  | ok value => exact safe_fresh value (binary_value_minted 0 op ty lhs rhs value computed)

private theorem safe_binary_bool (op : BinOp) (left right : ValueId) :
    Safe (fun _ => True) (semBoolBinOpInst op left right) := by
  unfold semBoolBinOpInst
  refine safe_bind _ _ _ _ (safe_lookup left) ?_
  intro lhs _
  refine safe_bind _ _ _ _ (safe_lookup right) ?_
  intro rhs _
  cases computed : semBoolBinOpValues op lhs rhs with
  | error error => exact safe_throw _ error
  | ok value => exact safe_fresh value (bool_binary_minted 0 op lhs rhs value computed)

private theorem safe_binary_minmax (op : BinOp) (ty : Ty) (left right : ValueId) :
    Safe (fun _ => True) (semFloatMinMax op ty left right) := by
  unfold semFloatMinMax
  refine safe_bind _ _ _ _ (safe_lookup left) ?_
  intro lhs _
  refine safe_bind _ _ _ _ (safe_lookup right) ?_
  intro rhs _
  exact safe_bind _ _ _ _ (safe_minmax_values op ty lhs rhs) (fun value free => safe_fresh value free)

/-- The original binary primitive, including explicit-choice float min/max,
preserves recursive identity validity on every successful execution. -/
theorem WellMintedState.binary_success (s final : MachineState) (op : BinOp) (ty : Ty)
    (left right id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semBinOp op ty left right) s = .ok (id, final)) : WellMintedState final := by
  have safe : Safe (fun _ => True) (semBinOp op ty left right) := by
    unfold semBinOp
    cases chosen : op.isMinMax with
    | false => exact safe_binary_deterministic op ty left right
    | true => exact safe_binary_minmax op ty left right
  exact (safe s final id valid run).1

/-- Contextual Bool uses its own strict original value boundary. -/
theorem WellMintedState.bool_binary_success (s final : MachineState) (op : BinOp)
    (left right id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semBoolBinOpInst op left right) s = .ok (id, final)) : WellMintedState final :=
  (safe_binary_bool op left right s final id valid run).1

/-- The original contextual dispatch, including the Bool-specific boundary. -/
def binaryAction (op : BinOp) (ty : Ty) (left right : ValueId) : Sem ValueId :=
  match ty with
  | .Bool => semBoolBinOpInst op left right
  | _ => semBinOp op ty left right

theorem binary_step_eq (ctx : EvalContext) (op : BinOp) (ty : Ty) (left right : ValueId) :
    stepInstWithContext ctx (.BinOp op ty left right) = (do
      let id ← binaryAction op ty left right
      pure (.value (some id))) := by
  cases ty <;> rfl

theorem WellMintedState.binary_action_success (s final : MachineState) (op : BinOp) (ty : Ty)
    (left right id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (binaryAction op ty left right) s = .ok (id, final)) : WellMintedState final := by
  cases ty <;> first
    | exact WellMintedState.bool_binary_success s final op left right id valid run
    | exact WellMintedState.binary_success s final op _ left right id valid run

private theorem safe_fresh_pair (first second : Value)
    (firstFree : MintedValue 0 first) (secondFree : MintedValue 0 second) :
    Safe (fun _ => True) (Sem.bindFreshPair first second) := by
  unfold Sem.bindFreshPair
  refine safe_bind _ _ _ _ (safe_fresh first firstFree) ?_
  intro firstId _
  refine safe_bind _ _ _ _ (safe_fresh second secondFree) ?_
  intro secondId _
  exact safe_pure _ _ True.intro

private theorem safe_overflow (op : OverflowOp) (ty : Ty) (left right : ValueId) :
    Safe (fun _ => True) (semOverflow op ty left right) := by
  unfold semOverflow
  refine safe_bind _ _ _ _ (safe_lookup left) ?_
  intro lhs _
  refine safe_bind _ _ _ _ (safe_lookup right) ?_
  intro rhs _
  refine safe_bind _ _ _ _ (safe_reject lhs "OverflowOp") ?_
  intro unit _
  cases unit
  refine safe_bind _ _ _ _ (safe_reject rhs "OverflowOp") ?_
  intro unit _
  cases unit
  split
  · split
    · exact safe_throw _ _
    · split
      · exact safe_fresh_pair _ _ (mintedValue_int 0 _ _) (mintedValue_bool 0 _)
      · exact safe_throw _ _
  · exact safe_throw _ _

/-- Overflow arithmetic publishes two frame-free components through the actual
primitive; all original poison, width and operand checks remain in execution. -/
theorem WellMintedState.overflow_success (s final : MachineState) (op : OverflowOp)
    (ty : Ty) (left right : ValueId) (ids : ValueId × ValueId)
    (valid : WellMintedState s)
    (run : Sem.run (semOverflow op ty left right) s = .ok (ids, final)) :
    WellMintedState final :=
  (safe_overflow op ty left right s final ids valid run).1

end TrustIr.FrameLifetime

